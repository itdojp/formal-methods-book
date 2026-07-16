#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'USAGE'
Usage: tools/sby-check.sh --config CONFIG.sby --task bmc|prove|cover [--out-dir DIR] [--time-limit SECONDS] <design.sv> <expected-results.json>
USAGE
}

out_dir=""
config=""
task=""
time_limit=180
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --out-dir' >&2; usage >&2; exit 2; }
      out_dir="$2"; shift 2 ;;
    --config)
      [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --config' >&2; usage >&2; exit 2; }
      config="$2"; shift 2 ;;
    --task)
      [[ $# -ge 2 && "$2" =~ ^(bmc|prove|cover)$ ]] || { echo 'Missing or invalid value for --task (expected bmc|prove|cover)' >&2; usage >&2; exit 2; }
      task="$2"; shift 2 ;;
    --time-limit)
      [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ && "$2" -le 900 ]] || { echo 'Missing or invalid value for --time-limit (expected 1..900)' >&2; usage >&2; exit 2; }
      time_limit="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done
rtl_source="${1:-}"
expected="${2:-}"
if [[ -z "$config" || ! -f "$config" ]]; then
  echo "SBY config not found: ${config:-<missing>}" >&2; usage >&2; exit 2
fi
if [[ -z "$task" ]]; then
  echo 'Missing value for --task (expected bmc|prove|cover)' >&2; usage >&2; exit 2
fi
if [[ -z "$rtl_source" || ! -f "$rtl_source" || "$rtl_source" != *.sv ]]; then
  echo "SBY RTL source not found or not a .sv file: ${rtl_source:-<missing>}" >&2; usage >&2; exit 2
fi
if [[ -z "$expected" || ! -f "$expected" ]]; then
  echo "SBY expected-results contract not found: ${expected:-<missing>}" >&2; usage >&2; exit 2
fi
if [[ $# -ne 2 ]]; then
  echo 'SBY check accepts exactly one RTL source and one expected-results contract' >&2; usage >&2; exit 2
fi
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/sby/$(basename "$config" .sby)-$task"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
artifact_root="$REPO_ROOT/.artifacts"
out_dir="$(realpath -m "$out_dir")"
case "$out_dir" in
  "$artifact_root"/*) ;;
  *) echo 'SBY --out-dir must be under the repository .artifacts directory' >&2; usage >&2; exit 2 ;;
esac
safe_input_path() {
  local candidate="$(realpath -e "$1")"
  case "$candidate" in
    "$REPO_ROOT"/*) printf '%s\n' "$candidate" ;;
    *) echo "SBY input must be under the repository root: $1" >&2; return 2 ;;
  esac
}
config="$(safe_input_path "$config")"
rtl_source="$(safe_input_path "$rtl_source")"
expected="$(safe_input_path "$expected")"
if [[ "$(dirname "$config")" != "$(dirname "$rtl_source")" ]]; then
  echo 'SBY config and RTL source must be in the same repository directory' >&2
  exit 2
fi
if ! node - "$REPO_ROOT" "$expected" "$task" "$config" "$rtl_source" <<'NODE'
const fs = require('fs');
const path = require('path');
const repoRoot = process.argv[2];
const { validateExpected } = require(path.join(repoRoot, 'scripts/validate-sby-results'));
try {
  const expected = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
  validateExpected(expected);
  if (expected.task !== process.argv[4]) throw new Error(`expected task ${expected.task} does not match --task ${process.argv[4]}`);
  const config = fs.readFileSync(process.argv[5], 'utf8').replace(/\r\n/g, '\n');
  const task = process.argv[4];
  const sourceName = path.basename(process.argv[6]);
  const depth = String(expected.depth);
  if (!/^[A-Za-z0-9][A-Za-z0-9._-]*\.sv$/.test(sourceName)) throw new Error(`unsupported RTL source name: ${sourceName}`);

  // An SBY file contains a Yosys script, and Yosys supports shell escapes.
  // Parse this repository's complete teaching-profile grammar rather than only
  // checking that a few required lines happen to be present.
  const sectionOrder = ['tasks', 'options', 'engines', 'script', 'files'];
  const sections = new Map(sectionOrder.map((name) => [name, []]));
  const seenSections = [];
  let current = null;
  for (const originalLine of config.split('\n')) {
    const line = originalLine.trim();
    if (line === '') continue;
    const heading = line.match(/^\[([a-z]+)\]$/);
    if (heading) {
      if (!sections.has(heading[1])) throw new Error(`unsupported SBY section: ${line}`);
      if (seenSections.includes(heading[1])) throw new Error(`duplicate SBY section: ${line}`);
      current = heading[1];
      seenSections.push(current);
      continue;
    }
    if (!current) throw new Error(`content outside an SBY section: ${line}`);
    sections.get(current).push(line);
  }
  if (JSON.stringify(seenSections) !== JSON.stringify(sectionOrder)) {
    throw new Error(`SBY sections must appear exactly as ${sectionOrder.map((name) => `[${name}]`).join(', ')}`);
  }

  const tasks = sections.get('tasks');
  if (tasks.length === 0 || new Set(tasks).size !== tasks.length || tasks.some((name) => !['bmc', 'prove', 'cover'].includes(name))) {
    throw new Error('SBY tasks must be a non-empty unique subset of bmc, prove, and cover');
  }
  if (!tasks.includes(task)) throw new Error(`SBY config does not declare selected task: ${task}`);
  const requireExact = (section, wanted) => {
    const actual = sections.get(section);
    if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
      throw new Error(`SBY [${section}] does not match the allowlisted teaching profile`);
    }
  };
  requireExact('options', tasks.flatMap((name) => [`${name}: mode ${name}`, `${name}: depth ${depth}`]));
  requireExact('engines', tasks.map((name) => `${name}: smtbmc bitwuzla`));
  requireExact('script', [`read -formal -sv ${sourceName}`, 'prep -top arbiter']);
  requireExact('files', [sourceName]);
  if (config.includes('\0')) {
    throw new Error('SBY config contains a NUL byte');
  }
} catch (error) {
  console.error(`Invalid SBY config/expected contract: ${error.message}`);
  process.exit(2);
}
NODE
then
  usage >&2
  exit 2
fi
command -v timeout >/dev/null 2>&1 || { echo 'SBY check requires coreutils timeout' >&2; exit 2; }

bash "$REPO_ROOT/tools/bootstrap.sh" --tool sby
suite_version="$(tool_manifest_field sby suiteVersion)"
suite_dir="$REPO_ROOT/tools/.tmp/oss-cad-suite-${suite_version}/oss-cad-suite"
sby_bin="$suite_dir/bin/sby"
[[ -x "$sby_bin" ]] || { echo "SBY binary not found after bootstrap: $sby_bin" >&2; exit 1; }

rm -rf "$out_dir"
mkdir -p "$out_dir"
work_dir="$(mktemp -d "$REPO_ROOT/tools/.tmp/sby-${task}-XXXXXX")"
raw_log="$work_dir/sby.raw.log"
results_json="$out_dir/results.json"
summary_log="$out_dir/summary.log"
cleanup() { rm -rf "$work_dir"; }
trap cleanup EXIT

set +e
# Use the pinned suite launchers without overriding the process dynamic-loader environment.
(cd "$(dirname "$config")" && \
  timeout --signal=TERM --kill-after=10s "${time_limit}s" \
    "$sby_bin" -f -d "$work_dir/work" "$(basename "$config")" "$task") >"$raw_log" 2>&1
sby_status=$?
set -e
if [[ $sby_status -eq 124 ]]; then
  cat "$raw_log" >&2
  echo "SBY reached the ${time_limit}s time limit" >&2
  exit 124
fi
if [[ $sby_status -ne 0 && $sby_status -ne 2 ]]; then
  cat "$raw_log" >&2
  echo "SBY exited with status $sby_status" >&2
  exit "$sby_status"
fi

set +e
validation_output="$(node "$REPO_ROOT/scripts/validate-sby-results.js" \
  "$raw_log" "$expected" "$work_dir/work" "$results_json" "$summary_log" "$REPO_ROOT" "$time_limit" 2>&1)"
validation_status=$?
set -e
if [[ $validation_status -ne 0 ]]; then
  printf '%s\n' "$validation_output" >&2
  cat "$raw_log" >&2
  rm -f "$results_json" "$summary_log"
  exit "$validation_status"
fi
trace_source="$(node -e 'const fs=require("fs"); const x=JSON.parse(fs.readFileSync(process.argv[1], "utf8")); process.stdout.write(x.trace?.source || "")' "$results_json")"
if [[ -n "$trace_source" ]]; then
  trace_path="$work_dir/work/$trace_source"
  [[ -f "$trace_path" ]] || { echo "Validated SBY trace disappeared: $trace_source" >&2; exit 1; }
  max_trace_bytes="$(node - "$REPO_ROOT/tools/tool-manifest.json" <<'NODE'
const fs = require('fs');
const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const value = manifest?.policy?.artifact?.maxBytesPerExample;
if (!Number.isSafeInteger(value) || value <= 0) throw new Error('invalid policy.artifact.maxBytesPerExample');
process.stdout.write(String(value));
NODE
)"
  trace_bytes="$(stat -c %s -- "$trace_path")"
  if [[ "$trace_bytes" -gt "$max_trace_bytes" ]]; then
    rm -f "$results_json" "$summary_log"
    echo "Validated SBY trace exceeds the per-example artifact limit: $trace_bytes > $max_trace_bytes bytes" >&2
    exit 1
  fi
  cp -- "$trace_path" "$out_dir/trace.vcd"
fi
printf '%s\n' "$validation_output"
cat "$summary_log"
echo "SBY result contract passed: $(node -e 'const fs=require("fs"); const x=JSON.parse(fs.readFileSync(process.argv[1], "utf8")); process.stdout.write(`${x.result} (${x.task} depth ${x.depth})`)' "$results_json")"

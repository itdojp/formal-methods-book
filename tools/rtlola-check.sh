#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'USAGE'
Usage: tools/rtlola-check.sh [--out-dir DIR] [--time-limit SECONDS] <property.lola> <trace.csv> <expected-results.json>
USAGE
}

out_dir=""
time_limit=60
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --out-dir' >&2; usage >&2; exit 2; }
      out_dir="$2"; shift 2 ;;
    --time-limit)
      [[ $# -ge 2 && "$2" =~ ^[1-9][0-9]*$ && "$2" -le 900 ]] || { echo 'Missing or invalid value for --time-limit (expected 1..900)' >&2; usage >&2; exit 2; }
      time_limit="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

specification=""
trace=""
expected_results=""
[[ $# -ge 1 ]] && specification="$1"
[[ $# -ge 2 ]] && trace="$2"
[[ $# -ge 3 ]] && expected_results="$3"
if [[ -z "$specification" || ! -f "$specification" || "$specification" != *.lola ]]; then
  echo "RTLola specification not found or not a .lola file: $specification" >&2
  usage >&2
  exit 2
fi
if [[ -z "$trace" || ! -f "$trace" || "$trace" != *.csv ]]; then
  echo "RTLola trace not found or not a .csv file: $trace" >&2
  usage >&2
  exit 2
fi
if [[ -z "$expected_results" || ! -f "$expected_results" || "$expected_results" != *.json ]]; then
  echo "RTLola expected-results contract not found or not JSON: $expected_results" >&2
  usage >&2
  exit 2
fi

if [[ $# -ne 3 ]]; then
  echo 'RTLola check accepts exactly one specification, trace, and expected-results contract' >&2
  usage >&2
  exit 2
fi

specification="$(realpath -e "$specification")"
trace="$(realpath -e "$trace")"
expected_results="$(realpath -e "$expected_results")"
for input in "$specification" "$trace" "$expected_results"; do
  case "$input" in
    "$REPO_ROOT"/*) ;;
    *) echo 'RTLola inputs must be under the repository root' >&2; usage >&2; exit 2 ;;
  esac
done

if LC_ALL=C grep -Eq -- 'AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{20,}|-----BEGIN [A-Z ]*PRIVATE KEY-----|sk-[A-Za-z0-9]{20,}' \
    "$specification" "$trace" "$expected_results"; then
  echo 'RTLola inputs contain a prohibited credential-like marker' >&2
  exit 2
fi

node - "$REPO_ROOT" "$specification" "$trace" "$expected_results" <<'NODE'
const fs = require('fs');
const validator = require(process.argv[2] + '/scripts/validate-rtlola-results');
try {
  const spec = fs.readFileSync(process.argv[3], 'utf8').replaceAll('\r\n', '\n');
  const trace = fs.readFileSync(process.argv[4], 'utf8').replaceAll('\r\n', '\n');
  const contract = JSON.parse(fs.readFileSync(process.argv[5], 'utf8'));
  validator.validateSpec(spec);
  const rows = validator.parseTrace(trace);
  const expected = validator.parseContract(contract);
  const derived = validator.deriveViolations(rows);
  if (JSON.stringify(expected.expectedViolations) !== JSON.stringify(derived)) {
    throw new Error('expected violation contract does not match the trace semantics');
  }
} catch (error) {
  console.error('Invalid RTLola teaching input: ' + error.message);
  process.exit(2);
}
NODE

command -v timeout >/dev/null 2>&1 || { echo 'RTLola check requires coreutils timeout' >&2; exit 2; }

if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/rtlola/$(basename "$trace" .csv)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
artifact_root="$REPO_ROOT/.artifacts"
out_dir="$(realpath -m "$out_dir")"
case "$out_dir" in
  "$artifact_root"/*) ;;
  *) echo 'RTLola --out-dir must be under the repository .artifacts directory' >&2; usage >&2; exit 2 ;;
esac

mkdir -p "$out_dir"
if [[ ! -d "$out_dir" || -L "$out_dir" ]]; then
  echo 'RTLola --out-dir must be a regular directory' >&2
  exit 2
fi
results_json="$out_dir/results.json"
violation_report="$out_dir/violation-report.json"
summary_log="$out_dir/summary.log"
unexpected_output="$(find "$out_dir" -mindepth 1 -maxdepth 1 \
  ! -name 'results.json' ! -name 'violation-report.json' ! -name 'summary.log' \
  -print -quit)"
if [[ -n "$unexpected_output" ]]; then
  echo "RTLola --out-dir must be empty or contain only prior RTLola outputs: $unexpected_output" >&2
  exit 2
fi
for output_file in "$results_json" "$violation_report" "$summary_log"; do
  if [[ -d "$output_file" && ! -L "$output_file" ]]; then
    echo "RTLola prior output path must not be a directory: $output_file" >&2
    exit 2
  fi
  rm -f -- "$output_file"
done

bash "$REPO_ROOT/tools/bootstrap.sh" --tool rtlola
version="$(tool_manifest_field rtlola version)"
commit="$(tool_manifest_field rtlola commit)"
rust_toolchain="$(tool_manifest_field rtlola rustToolchain)"
rtlola_bin="$REPO_ROOT/tools/.tmp/rtlola-$version/target/release/rtlola-cli"
if [[ ! -x "$rtlola_bin" || -L "$rtlola_bin" ]]; then
  echo 'RTLola binary is missing after bootstrap' >&2
  exit 1
fi

work_dir="$(mktemp -d "$REPO_ROOT/tools/.tmp/rtlola-check-XXXXXX")"
analysis_raw="$work_dir/analysis.raw"
monitor_raw="$work_dir/monitor.raw"
cleanup() { rm -rf "$work_dir"; }
trap cleanup EXIT

set +e
(
  ulimit -f 136
  timeout --signal=TERM --kill-after=10s "$time_limit"s \
    "$rtlola_bin" analyze "$specification"
) >"$analysis_raw" 2>&1
analysis_status=$?
set -e
if [[ $analysis_status -ne 0 ]]; then
  sed "s#$REPO_ROOT#<repo>#g" "$analysis_raw" >&2
  if [[ $analysis_status -eq 124 ]]; then
    echo "RTLola analysis reached the $time_limit second time limit" >&2
  else
    echo "RTLola analysis exited with status $analysis_status" >&2
  fi
  exit "$analysis_status"
fi
if [[ "$(wc -c < "$analysis_raw")" -gt 65536 ]]; then
  echo 'RTLola analysis output exceeds the 64 KiB contract' >&2
  exit 125
fi

set +e
(
  ulimit -f 136
  timeout --signal=TERM --kill-after=10s "$time_limit"s \
    "$rtlola_bin" monitor "$specification" \
    --offline relative-float-secs \
    --csv-in "$trace" \
    --stdout \
    --verbosity violations \
    --output-format json
) >"$monitor_raw" 2>&1
monitor_status=$?
set -e
if [[ $monitor_status -ne 0 ]]; then
  sed "s#$REPO_ROOT#<repo>#g" "$monitor_raw" >&2
  if [[ $monitor_status -eq 124 ]]; then
    echo "RTLola monitoring reached the $time_limit second time limit" >&2
  else
    echo "RTLola monitoring exited with status $monitor_status" >&2
  fi
  exit "$monitor_status"
fi
if [[ "$(wc -c < "$monitor_raw")" -gt 65536 ]]; then
  echo 'RTLola monitor output exceeds the 64 KiB contract' >&2
  exit 125
fi

node "$REPO_ROOT/scripts/validate-rtlola-results.js" \
  "$monitor_raw" "$specification" "$trace" "$expected_results" \
  "$results_json" "$violation_report" "$summary_log" \
  "$version" "$commit" "$rust_toolchain" "$time_limit"

cat "$summary_log"
result="$(node -e 'const fs=require("fs"); process.stdout.write(JSON.parse(fs.readFileSync(process.argv[1], "utf8")).result)' "$results_json")"
violation_count="$(node -e 'const fs=require("fs"); process.stdout.write(String(JSON.parse(fs.readFileSync(process.argv[1], "utf8")).violations.length))' "$results_json")"
violation_label='violations'
[[ "$violation_count" == '1' ]] && violation_label='violation'
echo "RTLola runtime contract passed: $result ($violation_count $violation_label)"

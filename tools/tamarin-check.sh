#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'USAGE'
Usage: tools/tamarin-check.sh [--out-dir DIR] [--time-limit SECONDS] <model.spthy> <expected-results.json>
USAGE
}

out_dir=""
time_limit=150
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      if [[ $# -lt 2 || "$2" == -* ]]; then
        echo 'Missing value for --out-dir' >&2
        usage >&2
        exit 2
      fi
      out_dir="$2"
      shift 2
      ;;
    --time-limit)
      if [[ $# -lt 2 || ! "$2" =~ ^[1-9][0-9]*$ || "$2" -gt 900 ]]; then
        echo 'Missing or invalid value for --time-limit (expected 1..900)' >&2
        usage >&2
        exit 2
      fi
      time_limit="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    -*)
      echo "Unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

model="${1:-}"
expected_results="${2:-}"
if [[ -z "$model" || ! -f "$model" ]]; then
  echo "Tamarin model not found: ${model:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ -z "$expected_results" || ! -f "$expected_results" ]]; then
  echo "Tamarin expected-results contract not found: ${expected_results:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ $# -ne 2 ]]; then
  echo 'Tamarin check accepts exactly one model and one expected-results contract' >&2
  usage >&2
  exit 2
fi
# Attack-graph artifacts preserve symbolic constants from the model. Reject
# common credential formats before execution; this is a narrow guardrail, not
# a substitute for reviewing every teaching model as public input.
if LC_ALL=C grep -Eq -- 'AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{20,}|-----BEGIN [A-Z ]*PRIVATE KEY-----|sk-[A-Za-z0-9]{20,}' \
    "$model" "$expected_results"; then
  echo 'Tamarin inputs contain a prohibited credential-like marker' >&2
  exit 2
fi
command -v timeout >/dev/null 2>&1 || {
  echo 'Tamarin check requires coreutils timeout' >&2
  exit 2
}

bash "$REPO_ROOT/tools/bootstrap.sh" --tool tamarin
tamarin_version="$(tool_manifest_field tamarin version)"
maude_version="$(tool_manifest_field tamarin maudeVersion)"
tamarin_bin="$REPO_ROOT/tools/.cache/tamarin-${tamarin_version}/tamarin-prover"
maude_bin="$REPO_ROOT/tools/.cache/maude-${maude_version}/maude"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/tamarin/$(basename "$model" .spthy)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
mkdir -p "$out_dir"
raw_log="$out_dir/.tamarin-results.raw"
raw_graph="$out_dir/.tamarin-graphs.raw.json"
results_json="$out_dir/results.json"
summary_log="$out_dir/tamarin-summary.log"
attack_json="$out_dir/attack-trace.json"
rm -f "$raw_log" "$raw_graph" "$results_json" "$summary_log" "$attack_json"

set +e
timeout --signal=TERM --kill-after=10s "${time_limit}s" \
  "$tamarin_bin" \
  --with-maude="$maude_bin" \
  --quit-on-warning \
  --prove \
  --stop-on-trace=SEQDFS \
  --output-json="$raw_graph" \
  "$model" >"$raw_log" 2>&1
status=$?
set -e
if [[ $status -ne 0 ]]; then
  sed "s#${REPO_ROOT}#<repo>#g" "$raw_log" >&2
  rm -f "$raw_log" "$raw_graph"
  if [[ $status -eq 124 ]]; then
    echo "Tamarin reached the ${time_limit}s time limit" >&2
  else
    echo "Tamarin exited with status $status" >&2
  fi
  exit "$status"
fi
if [[ ! -s "$raw_graph" ]]; then
  echo 'Tamarin did not produce graph JSON' >&2
  rm -f "$raw_log" "$raw_graph"
  exit 1
fi

set +e
node "$REPO_ROOT/scripts/validate-tamarin-results.js" \
  "$raw_log" "$raw_graph" "$model" "$expected_results" \
  "$results_json" "$summary_log" "$attack_json" "$time_limit"
validation_status=$?
set -e
if [[ $validation_status -ne 0 ]]; then
  # Retain only sanitized diagnostics; raw Tamarin output can contain absolute
  # runner paths and must not survive a failed contract comparison.
  sed "s#${REPO_ROOT}#<repo>#g" "$raw_log" >&2
  rm -f "$raw_log" "$raw_graph" "$results_json" "$summary_log" "$attack_json"
  exit "$validation_status"
fi
rm -f "$raw_log" "$raw_graph"
cat "$summary_log"
result="$(node -e 'const fs=require("fs"); process.stdout.write(JSON.parse(fs.readFileSync(process.argv[1], "utf8")).result)' "$results_json")"
lemma_count="$(node -e 'const fs=require("fs"); process.stdout.write(String(JSON.parse(fs.readFileSync(process.argv[1], "utf8")).lemmas.length))' "$results_json")"
echo "Tamarin result contract passed: $result ($lemma_count lemmas)"

#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'USAGE'
Usage: tools/cvc5-proof-check.sh [--out-dir DIR] [--time-limit SECONDS] <contradiction.smt2>
USAGE
}

out_dir=""
time_limit=120
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

input="${1:-}"
if [[ $# -ne 1 || -z "$input" || ! -f "$input" || "$input" != *.smt2 ]]; then
  echo "cvc5 SMT2 input not found or not a .smt2 file: ${input:-<missing>}" >&2
  usage >&2
  exit 2
fi
input="$(realpath -e "$input")"
case "$input" in "$REPO_ROOT"/*) ;; *) echo 'cvc5 input must be under the repository root' >&2; usage >&2; exit 2 ;; esac

if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/cvc5/$(basename "$input" .smt2)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
artifact_root="$REPO_ROOT/.artifacts"
out_dir="$(realpath -m "$out_dir")"
case "$out_dir" in "$artifact_root"/*) ;; *) echo 'cvc5 --out-dir must be under the repository .artifacts directory' >&2; usage >&2; exit 2 ;; esac

# The wrapper accepts one fixed teaching grammar only. This rules out SMT-LIB
# options such as get-model/get-proof, redirection, includes, or extra commands.
node - "$REPO_ROOT" "$input" <<'NODE'
const fs = require('fs');
const { validateTinySmt2 } = require(`${process.argv[2]}/scripts/validate-cvc5-proof-results`);
try {
  validateTinySmt2(fs.readFileSync(process.argv[3], 'utf8'));
} catch (error) {
  console.error(`Invalid cvc5 teaching input: ${error.message}`);
  process.exit(2);
}
NODE

command -v timeout >/dev/null 2>&1 || { echo 'cvc5 proof check requires coreutils timeout' >&2; exit 2; }
bash "$REPO_ROOT/tools/bootstrap.sh" --tool cvc5
version="$(tool_manifest_field cvc5 version)"
checker_version="$(tool_manifest_field cvc5 checkerVersion)"
max_certificate_bytes="$(tool_manifest_field cvc5 maxCertificateBytes)"
max_checker_output_bytes="$(tool_manifest_field cvc5 maxCheckerOutputBytes)"
cvc5_bin="$REPO_ROOT/tools/.cache/cvc5-${version}/bin/cvc5"
carcara_bin="$REPO_ROOT/tools/.tmp/carcara-${checker_version}/target/release/carcara"
[[ -x "$cvc5_bin" && -x "$carcara_bin" ]] || { echo 'cvc5 or Carcara binary missing after bootstrap' >&2; exit 1; }

rm -rf "$out_dir"
mkdir -p "$out_dir"
work_dir="$(mktemp -d "$REPO_ROOT/tools/.tmp/cvc5-proof-XXXXXX")"
solver_raw="$work_dir/cvc5.raw"
checker_raw="$work_dir/carcara.raw"
results_json="$out_dir/results.json"
summary_log="$out_dir/summary.log"
certificate="$out_dir/certificate.alethe"
cleanup() { rm -rf "$work_dir"; }
trap cleanup EXIT

set +e
( ulimit -f $(( (max_certificate_bytes + 4096 + 511) / 512 ));
  timeout --signal=TERM --kill-after=10s "${time_limit}s" \
    "$cvc5_bin" --lang smt2 --produce-proofs --dump-proofs --proof-format-mode=alethe "$input" ) >"$solver_raw" 2>&1
solver_status=$?
set -e

checker_status=-1
if [[ $solver_status -eq 0 ]] && head -n 1 "$solver_raw" | grep -Fxq 'unsat'; then
  if node "$REPO_ROOT/scripts/validate-cvc5-proof-results.js" extract "$solver_raw" "$certificate" "$max_certificate_bytes"; then
    set +e
    ( ulimit -f $(( (max_checker_output_bytes + 511) / 512 ));
      timeout --signal=TERM --kill-after=10s "${time_limit}s" \
        "$carcara_bin" check "$certificate" "$input" ) >"$checker_raw" 2>&1
    checker_status=$?
    set -e
    if [[ -f "$checker_raw" && "$(wc -c < "$checker_raw")" -gt "$max_checker_output_bytes" ]]; then
      checker_status=125
    fi
  fi
fi

node "$REPO_ROOT/scripts/validate-cvc5-proof-results.js" write \
  "$solver_raw" "$input" "$checker_raw" "$solver_status" "$checker_status" \
  "$results_json" "$summary_log" "$time_limit"
result="$(node -e 'const x=require(process.argv[1]); process.stdout.write(x.result)' "$results_json")"
cat "$summary_log"
if [[ "$result" == 'success' ]]; then
  echo 'cvc5 Alethe proof certificate passed: independently checked by Carcara'
  exit 0
fi
echo "cvc5 Alethe proof certificate failed: $result" >&2
[[ "$result" == 'solver-timeout' || "$result" == 'checker-timeout' ]] && exit 124
exit 1

#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'EOF'
Usage: tools/prism-check.sh [--out-dir DIR] <model.pm> <properties.props> <expected-results.json>
EOF
}

out_dir=""
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
properties="${2:-}"
expected_results="${3:-}"
if [[ -z "$model" || ! -f "$model" ]]; then
  echo "PRISM model not found: ${model:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ -z "$properties" || ! -f "$properties" ]]; then
  echo "PRISM properties not found: ${properties:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ -z "$expected_results" || ! -f "$expected_results" ]]; then
  echo "PRISM expected-results contract not found: ${expected_results:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ $# -ne 3 ]]; then
  echo 'PRISM check accepts exactly one model, properties file, and expected-results contract' >&2
  usage >&2
  exit 2
fi

bash "$REPO_ROOT/tools/bootstrap.sh" --tool prism
version="$(tool_manifest_field prism version)"
prism_bin="$REPO_ROOT/tools/.cache/prism-${version}/bin/prism"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/prism/$(basename "$model" .pm)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
mkdir -p "$out_dir"
raw_output="$out_dir/prism-results.log"
raw_capture="$out_dir/.prism-results.raw"
result_json="$out_dir/results.json"

set +e
"$prism_bin" "$model" "$properties" -explicit >"$raw_capture" 2>&1
status=$?
set -e
# PRISM's banner includes wall-clock and host values that do not affect the
# result. Remove them from retained evidence to keep artifacts reproducible and
# avoid disclosing runner identifiers.
sed -E '/^Date:/d; /^Hostname:/d' "$raw_capture" >"$raw_output"
rm -f "$raw_capture"
cat "$raw_output"
if [[ $status -ne 0 ]]; then
  echo "PRISM exited with status $status" >&2
  exit "$status"
fi

node "$REPO_ROOT/scripts/validate-prism-results.js" \
  "$raw_output" "$result_json" "$version" "$expected_results"

result_count="$(node -e 'const fs=require("fs"); const value=JSON.parse(fs.readFileSync(process.argv[1], "utf8")); process.stdout.write(String(value.results.length))' "$expected_results")"
echo "PRISM result contract passed: $result_count properties"

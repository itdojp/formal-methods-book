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

node - "$raw_output" "$result_json" "$version" "$expected_results" <<'NODE'
'use strict';

const fs = require('fs');

const inputPath = process.argv[2];
const outputPath = process.argv[3];
const expectedVersion = process.argv[4];
const contractPath = process.argv[5];
const text = fs.readFileSync(inputPath, 'utf8');
const contract = JSON.parse(fs.readFileSync(contractPath, 'utf8'));
if (contract.schemaVersion !== 1
    || typeof contract.modelType !== 'string'
    || contract.engine !== 'explicit'
    || !Number.isFinite(contract.tolerance)
    || contract.tolerance <= 0
    || contract.tolerance > 1e-6
    || !Array.isArray(contract.results)
    || contract.results.length === 0) {
  throw new Error('Invalid PRISM expected-results contract');
}
const escapedVersion = expectedVersion.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const escapedModelType = contract.modelType.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
if (!new RegExp(`^Version:\\s+${escapedVersion}$`, 'm').test(text)
    || !new RegExp(`^Type:\\s+${escapedModelType}$`, 'm').test(text)) {
  throw new Error('PRISM version/model type marker is missing');
}

const actual = Array.from(text.matchAll(/^Result:\s+([^\r\n]+)$/gm), (match) => match[1].trim());
if (actual.length !== contract.results.length) {
  throw new Error(`Expected ${contract.results.length} PRISM results, found ${actual.length}`);
}

const numberFrom = (value) => {
  const numeric = Number(value.replace(/\s+\(.*\)$/, ''));
  if (!Number.isFinite(numeric)) throw new Error(`Expected numeric PRISM result, got: ${value}`);
  return numeric;
};
const results = contract.results.map((item, index) => {
  if (!item || typeof item.property !== 'string' || item.property.length === 0
      || !['boolean', 'number'].includes(typeof item.expected)) {
    throw new Error(`Invalid expected result at index ${index}`);
  }
  let actualValue;
  if (typeof item.expected === 'boolean') {
    if (!/^(?:true|false)$/.test(actual[index])) {
      throw new Error(`Expected boolean PRISM result at index ${index}, got: ${actual[index]}`);
    }
    actualValue = actual[index] === 'true';
    if (actualValue !== item.expected) {
      throw new Error(`Boolean result mismatch for ${item.property}: ${actualValue}`);
    }
  } else {
    actualValue = numberFrom(actual[index]);
    if (Math.abs(actualValue - item.expected) > contract.tolerance) {
      throw new Error(`Numeric result mismatch for ${item.property}: ${actualValue}`);
    }
  }
  return { property: item.property, expected: item.expected, actual: actualValue };
});

const report = {
  schemaVersion: 1,
  tool: 'PRISM',
  toolVersion: expectedVersion,
  modelType: contract.modelType,
  engine: contract.engine,
  tolerance: contract.tolerance,
  results,
};
fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
NODE

result_count="$(node -e 'const fs=require("fs"); const value=JSON.parse(fs.readFileSync(process.argv[1], "utf8")); process.stdout.write(String(value.results.length))' "$expected_results")"
echo "PRISM result contract passed: $result_count properties"

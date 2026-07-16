#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"
bash "$REPO_ROOT/tools/bootstrap.sh" --tool cbmc

CBMC_VERSION="$(tool_manifest_field cbmc version)"
CBMC_BIN="$REPO_ROOT/tools/.cache/cbmc-${CBMC_VERSION}/usr/bin/cbmc"

usage() {
  echo 'Usage: tools/cbmc-check.sh <file.c>'
}

file="${1:-}"
if [[ -z "$file" || ! -f "$file" ]]; then
  echo "C file not found: ${file:-<missing>}" >&2
  usage >&2
  exit 2
fi

echo "CBMC: $file"
"$CBMC_BIN" \
  --bounds-check \
  --pointer-check \
  --signed-overflow-check \
  --unwinding-assertions \
  "$file"

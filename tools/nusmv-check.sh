#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"
bash "$REPO_ROOT/tools/bootstrap.sh" --tool nusmv

NUSMV_VERSION="$(tool_manifest_field nusmv version)"
NUSMV_DIR="$REPO_ROOT/tools/.cache/nusmv-${NUSMV_VERSION}"
NUSMV_BIN="$NUSMV_DIR/bin/NuSMV"

usage() {
  echo 'Usage: tools/nusmv-check.sh <model.smv>'
}

model="${1:-}"
if [[ -z "$model" || ! -f "$model" ]]; then
  echo "Model not found: ${model:-<missing>}" >&2
  usage >&2
  exit 2
fi

library_path=""
if [[ -d "$NUSMV_DIR/lib" ]]; then
  while IFS= read -r directory; do
    library_path="${library_path:+$library_path:}$directory"
  done < <(find "$NUSMV_DIR/lib" -type d -print | sort)
fi

echo "NuSMV: $model"
if [[ -n "$library_path" ]]; then
  LD_LIBRARY_PATH="${library_path}${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" "$NUSMV_BIN" "$model"
else
  "$NUSMV_BIN" "$model"
fi

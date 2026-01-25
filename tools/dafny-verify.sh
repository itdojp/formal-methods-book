#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Ensure tools are available.
bash "$REPO_ROOT/tools/bootstrap.sh" >/dev/null

: "${DAFNY_VERSION:=4.11.0}"
DAFNY_BIN="$REPO_ROOT/tools/.cache/dafny-${DAFNY_VERSION}/DafnyDriver"

usage() {
  cat <<'EOF'
Usage:
  tools/dafny-verify.sh <file.dfy>

Notes:
  - Uses the pinned Dafny binary distribution.
EOF
}

file="${1:-}"
if [[ -z "$file" ]]; then
  usage >&2
  exit 2
fi
if [[ ! -f "$file" ]]; then
  echo "Dafny file not found: $file" >&2
  exit 2
fi

if [[ ! -x "$DAFNY_BIN" ]]; then
  echo "DafnyDriver not found or not executable: $DAFNY_BIN" >&2
  echo "Hint: run 'bash tools/bootstrap.sh' (Linux/WSL/devcontainer). On macOS, use the official Dafny distribution or dotnet tool." >&2
  exit 2
fi

echo "Dafny verify: $file"
"$DAFNY_BIN" verify "$file"

#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Ensure tools are available.
bash "$REPO_ROOT/tools/bootstrap.sh" >/dev/null

: "${APALACHE_VERSION:=0.52.1}"
APALACHE_BIN="$REPO_ROOT/tools/.cache/apalache-${APALACHE_VERSION}/bin/apalache-mc"

usage() {
  cat <<'EOF'
Usage:
  tools/apalache-check.sh [--out-dir DIR] [--config FILE] [--length N] --init INIT --next NEXT --inv INV <spec.tla>

Notes:
  - This is a thin wrapper around `apalache-mc check`.
  - Outputs are written under --out-dir (default: .artifacts/apalache/<stem>/)
EOF
}

out_dir=""
cfg=""
init=""
next=""
inv=""
length=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      out_dir="${2:-}"; shift 2;;
    --config)
      cfg="${2:-}"; shift 2;;
    --length)
      length="${2:-}"; shift 2;;
    --init)
      init="${2:-}"; shift 2;;
    --next)
      next="${2:-}"; shift 2;;
    --inv)
      inv="${2:-}"; shift 2;;
    -h|--help)
      usage; exit 0;;
    -*)
      echo "Unknown option: $1" >&2
      usage >&2
      exit 2;;
    *)
      break;;
  esac
done

spec="${1:-}"
if [[ -z "$spec" || -z "$init" || -z "$next" || -z "$inv" ]]; then
  usage >&2
  exit 2
fi
if [[ ! -f "$spec" ]]; then
  echo "Spec not found: $spec" >&2
  exit 2
fi

stem="$(basename "$spec" .tla)"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/apalache/$stem"
fi
mkdir -p "$out_dir"

echo "Apalache check: $spec"
args=(check --out-dir="$out_dir" --init="$init" --next="$next" --inv="$inv")
if [[ -n "$cfg" ]]; then
  if [[ ! -f "$cfg" ]]; then
    echo "Config not found: $cfg" >&2
    exit 2
  fi
  args+=(--config="$cfg")
fi
if [[ -n "$length" ]]; then
  args+=(--length="$length")
fi

"$APALACHE_BIN" "${args[@]}" "$spec"

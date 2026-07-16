#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

usage() {
  cat <<'EOF'
Usage: tools/spin-check.sh [--out-dir DIR] [--claim NAME] <model.pml>
EOF
}

out_dir=""
claim=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      if [[ $# -lt 2 || "$2" == -* ]]; then
        echo "Missing value for --out-dir" >&2
        usage >&2
        exit 2
      fi
      out_dir="$2"
      shift 2
      ;;
    --claim)
      if [[ $# -lt 2 || "$2" == -* ]]; then
        echo "Missing value for --claim" >&2
        usage >&2
        exit 2
      fi
      claim="$2"
      shift 2
      ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

model="${1:-}"
if [[ -z "$model" || ! -f "$model" ]]; then
  echo "Model not found: ${model:-<missing>}" >&2
  usage >&2
  exit 2
fi

bash "$REPO_ROOT/tools/bootstrap.sh" --tool spin
: "${SPIN_VERSION:=6.5.2}"
SPIN_BIN="$REPO_ROOT/tools/.cache/spin-${SPIN_VERSION}/bin/spin"

if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/spin/$(basename "$model" .pml)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
if ! command -v cc >/dev/null 2>&1; then
  echo 'Required command not found: cc (install build-essential)' >&2
  exit 2
fi
model="$(cd "$(dirname "$model")" && pwd)/$(basename "$model")"
work_dir="$out_dir/work"
rm -rf "$work_dir"
mkdir -p "$work_dir"

echo "SPIN: $model"
(
  cd "$work_dir"
  "$SPIN_BIN" -a "$model"
  cc -O2 -o pan pan.c
  pan_args=(-a -m100000)
  if [[ -n "$claim" ]]; then
    pan_args=(-N "$claim" "${pan_args[@]}")
  fi
  ./pan "${pan_args[@]}"
)

#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Ensure tools are available.
bash "$REPO_ROOT/tools/bootstrap.sh" >/dev/null

: "${ALLOY_VERSION:=6.2.0}"
ALLOY_JAR="$REPO_ROOT/tools/.cache/alloy-${ALLOY_VERSION}.jar"

usage() {
  cat <<'EOF'
Usage:
  tools/alloy-check.sh [--out-dir DIR] [--command CMD] [--repeat N] [--solver NAME] <model.als>

Notes:
  - Outputs are written under --out-dir (default: .artifacts/alloy/<stem>/)
  - Uses Alloy CLI: `java -jar ... exec`
EOF
}

out_dir=""
command=""
repeat=""
solver=""
quiet=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      out_dir="${2:-}"; shift 2;;
    --command)
      command="${2:-}"; shift 2;;
    --repeat)
      repeat="${2:-}"; shift 2;;
    --solver)
      solver="${2:-}"; shift 2;;
    --verbose)
      quiet=0; shift;;
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

model="${1:-}"
if [[ -z "$model" ]]; then
  usage >&2
  exit 2
fi
if [[ ! -f "$model" ]]; then
  echo "Model not found: $model" >&2
  exit 2
fi

stem="$(basename "$model" .als)"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/alloy/$stem"
fi
mkdir -p "$out_dir"

args=(exec -f -o "$out_dir")
if [[ "$quiet" -eq 1 ]]; then
  args+=(-q)
fi
if [[ -n "$command" ]]; then
  args+=(-c "$command")
fi
if [[ -n "$repeat" ]]; then
  args+=(-r "$repeat")
fi
if [[ -n "$solver" ]]; then
  args+=(-s "$solver")
fi

echo "Alloy exec: $model"
java -jar "$ALLOY_JAR" "${args[@]}" "$model"

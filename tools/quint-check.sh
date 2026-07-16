#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'EOF'
Usage: tools/quint-check.sh [--out-dir DIR] [--seed N] [--max-samples N] <spec.qnt>
EOF
}

out_dir=""
seed=""
max_samples=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --out-dir' >&2; usage >&2; exit 2; }; out_dir="$2"; shift 2 ;;
    --seed) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --seed' >&2; usage >&2; exit 2; }; seed="$2"; shift 2 ;;
    --max-samples) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --max-samples' >&2; usage >&2; exit 2; }; max_samples="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

spec="${1:-}"
if [[ -z "$spec" || ! -f "$spec" ]]; then
  echo "Quint specification not found: ${spec:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ -z "$seed" || -z "$max_samples" || ! "$seed" =~ ^[0-9]+$ || ! "$max_samples" =~ ^[1-9][0-9]*$ ]]; then
  echo 'Quint checks require numeric --seed and positive --max-samples' >&2
  usage >&2
  exit 2
fi

bash "$REPO_ROOT/tools/bootstrap.sh" --tool quint
version="$(tool_manifest_field quint version)"
quint_bin="$REPO_ROOT/tools/.cache/quint-${version}/quint"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/quint/$(basename "$spec" .qnt)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
mkdir -p "$out_dir"

echo "Quint typecheck/test: $spec"
"$quint_bin" typecheck "$spec"
# The Rust evaluator is a separately downloaded component. Use the bundled
# TypeScript backend so the executable contract remains fully checksum-pinned.
"$quint_bin" --backend=typescript test \
  --seed="$seed" \
  --max-samples="$max_samples" \
  --out-itf "$out_dir/{test}_{seq}.itf.json" \
  "$spec"

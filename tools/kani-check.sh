#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

usage() {
  cat <<'EOF'
Usage: tools/kani-check.sh [--out-dir DIR] --harness NAME --unwind N <file.rs>
EOF
}

out_dir=""
harness=""
unwind=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --out-dir' >&2; usage >&2; exit 2; }; out_dir="$2"; shift 2 ;;
    --harness) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --harness' >&2; usage >&2; exit 2; }; harness="$2"; shift 2 ;;
    --unwind) [[ $# -ge 2 && "$2" != -* ]] || { echo 'Missing value for --unwind' >&2; usage >&2; exit 2; }; unwind="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

file="${1:-}"
if [[ -z "$file" || ! -f "$file" ]]; then
  echo "Rust source not found: ${file:-<missing>}" >&2
  usage >&2
  exit 2
fi
if [[ ! "$harness" =~ ^[A-Za-z_][A-Za-z0-9_]*$ || ! "$unwind" =~ ^[1-9][0-9]*$ ]]; then
  echo 'Kani checks require an identifier --harness and positive --unwind' >&2
  usage >&2
  exit 2
fi

bash "$REPO_ROOT/tools/bootstrap.sh" --tool kani
version="$(tool_manifest_field kani version)"
toolchain="$(tool_manifest_field kani rustToolchain)"
kani_dir="$REPO_ROOT/tools/.cache/kani-${version}"
rustup_home="$REPO_ROOT/tools/.cache/kani-rustup-${toolchain}"
cargo_home="$REPO_ROOT/tools/.cache/kani-cargo"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/kani/$(basename "$file" .rs)"
elif [[ "$out_dir" != /* ]]; then
  out_dir="$REPO_ROOT/$out_dir"
fi
mkdir -p "$out_dir"

export RUSTUP_HOME="$rustup_home"
export CARGO_HOME="$cargo_home"
sysroot="$(rustup run "$toolchain" rustc --print sysroot)"
export PATH="$kani_dir/bin:$PATH"
export LD_LIBRARY_PATH="$sysroot/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

echo "Kani proof: $file ($harness, unwind=$unwind)"
"$kani_dir/bin/kani-driver" \
  --harness "$harness" \
  --exact \
  --default-unwind "$unwind" \
  --target-dir "$out_dir/target" \
  "$file"

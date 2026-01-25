#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Ensure tools are available.
bash "$REPO_ROOT/tools/bootstrap.sh" >/dev/null

: "${TLA_VERSION:=1.7.4}"
TLA_JAR="$REPO_ROOT/tools/.cache/tla2tools-${TLA_VERSION}.jar"

usage() {
  cat <<'EOF'
Usage:
  tools/tlc-run.sh [--out-dir DIR] [--config FILE] [--workers N] [--depth N] [--seed N] [--time-limit SEC] <spec.tla>

Notes:
  - TLC is executed via: `java -cp tla2tools.jar tlc2.TLC ...`
  - Output log is saved to <out-dir>/tlc.log (default: .artifacts/tlc/<stem>/)
EOF
}

out_dir=""
cfg=""
workers="1"
depth=""
seed=""
time_limit=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out-dir)
      out_dir="${2:-}"; shift 2;;
    --config)
      cfg="${2:-}"; shift 2;;
    --workers)
      workers="${2:-}"; shift 2;;
    --depth)
      depth="${2:-}"; shift 2;;
    --seed)
      seed="${2:-}"; shift 2;;
    --time-limit)
      time_limit="${2:-}"; shift 2;;
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
if [[ -z "$spec" ]]; then
  usage >&2
  exit 2
fi
if [[ ! -f "$spec" ]]; then
  echo "Spec not found: $spec" >&2
  exit 2
fi

stem="$(basename "$spec" .tla)"
if [[ -z "$out_dir" ]]; then
  out_dir="$REPO_ROOT/.artifacts/tlc/$stem"
fi
mkdir -p "$out_dir"

log="$out_dir/tlc.log"

cmd=(java -cp "$TLA_JAR" tlc2.TLC -workers "$workers" -deadlock -metadir "$out_dir/metadir")
if [[ -n "$cfg" ]]; then
  if [[ ! -f "$cfg" ]]; then
    echo "Config not found: $cfg" >&2
    exit 2
  fi
  cmd+=(-config "$cfg")
fi
if [[ -n "$depth" ]]; then
  cmd+=(-depth "$depth")
fi
if [[ -n "$seed" ]]; then
  cmd+=(-seed "$seed")
fi
cmd+=("$spec")

echo "TLC: $spec"
echo "Log: $log"

if [[ -n "$time_limit" ]]; then
  # Prefer `timeout` when available (Linux/CI). If missing, run without limit.
  if command -v timeout >/dev/null 2>&1; then
    timeout "$time_limit" "${cmd[@]}" | tee "$log"
  else
    "${cmd[@]}" | tee "$log"
  fi
else
  "${cmd[@]}" | tee "$log"
fi

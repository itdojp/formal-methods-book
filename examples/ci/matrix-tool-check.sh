#!/usr/bin/env bash
set -euo pipefail

tool="${1:-}"
profile="${2:-}"
if [[ ! "$tool" =~ ^[a-z0-9]+(-[a-z0-9]+)*$ ]]; then
  echo "Invalid matrix tool: ${tool:-<missing>}" >&2
  exit 2
fi

case "$profile" in
  default)
    node scripts/run-example-manifest.js --tool "$tool"
    ;;
  nightly)
    node scripts/run-example-manifest.js --tool "$tool" --profile nightly
    ;;
  *)
    echo "Invalid matrix profile: ${profile:-<missing>}" >&2
    exit 2
    ;;
esac

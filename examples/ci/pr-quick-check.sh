#!/usr/bin/env bash
set -euo pipefail

# Minimal checks for PR: ensure example specs exist and include basic sections.

if ! command -v rg >/dev/null 2>&1; then
  echo "rg not found; falling back to grep" >&2
  grep -q "^sig" examples/alloy/collection.als
  grep -q "^Init" examples/tla/Queue.tla
  grep -q "^Next" examples/tla/Queue.tla
else
  rg -n "^sig" examples/alloy/collection.als >/dev/null
  rg -n "^Init" examples/tla/Queue.tla >/dev/null
  rg -n "^Next" examples/tla/Queue.tla >/dev/null
fi

echo "OK: minimal formal examples present"

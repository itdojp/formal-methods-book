#!/usr/bin/env bash
set -euo pipefail

# Minimal checks for PR: ensure example specs exist and include basic sections.
rg -n "^sig" examples/alloy/queue.als >/dev/null
rg -n "^Init" examples/tla/Queue.tla >/dev/null
rg -n "^Next" examples/tla/Queue.tla >/dev/null

echo "OK: minimal formal examples present"

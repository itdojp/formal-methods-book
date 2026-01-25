#!/usr/bin/env bash
set -euo pipefail

# Minimal executable checks for PR:
# - Alloy: parse+execute a tiny model (should be SAT)
# - TLC: model check a bounded TLA+ spec (should find no error)
# - Apalache: bounded check a tiny TLA+ spec (should find no error)
# - Dafny: verify a tiny Dafny file (should have 0 errors)

bash tools/bootstrap.sh

bash tools/alloy-check.sh examples/alloy/collection.als

bash tools/tlc-run.sh \
  --config examples/tla/QueueBounded.cfg \
  --time-limit 60 \
  examples/tla/QueueBounded.tla

bash tools/apalache-check.sh \
  --config examples/apalache/Counter.cfg \
  --length 10 \
  --init Init \
  --next Next \
  --inv Inv \
  examples/apalache/Counter.tla

bash tools/dafny-verify.sh examples/dafny/Abs.dfy

echo "OK: formal checks passed"


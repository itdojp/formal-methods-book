#!/usr/bin/env bash
set -euo pipefail

# The manifest is the only PR example inventory. Each wrapper bootstraps only
# its selected pr-quick tool, so SPIN/NuSMV/CBMC are not downloaded here.
node scripts/run-example-manifest.js --lane pr-quick

echo "OK: formal checks passed"

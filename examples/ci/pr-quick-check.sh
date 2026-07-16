#!/usr/bin/env bash
set -euo pipefail

# The manifest is the only PR example inventory. With no arguments all quick
# entries run (local/backward-compatible path). CI passes base/head refs so only
# entries related through assets, references, config, or wrappers are selected.
if [[ $# -eq 0 ]]; then
  node scripts/run-example-manifest.js --lane pr-quick
elif [[ $# -eq 2 && -n "$1" && -n "$2" ]]; then
  node scripts/run-example-manifest.js --lane pr-quick --changed-from "$1" --changed-to "$2"
else
  echo 'Usage: examples/ci/pr-quick-check.sh [BASE_REF HEAD_REF]' >&2
  exit 2
fi

echo "OK: formal checks passed"

#!/usr/bin/env bash

# This file is sourced by tool wrappers. Do not enable/disable shell options
# here because the caller owns its execution policy.

tool_manifest_field() {
  if [[ $# -ne 2 ]]; then
    echo 'tool_manifest_field requires TOOL and FIELD' >&2
    return 2
  fi
  node "$REPO_ROOT/scripts/tool-manifest.js" field "$1" "$2"
}

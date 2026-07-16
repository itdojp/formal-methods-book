#!/usr/bin/env bash

# This file is sourced by tool wrappers. Do not enable/disable shell options
# here because the caller owns its execution policy.

TOOL_MANIFEST_REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

tool_manifest_field() {
  if [[ $# -ne 2 ]]; then
    echo 'tool_manifest_field requires TOOL and FIELD' >&2
    return 2
  fi
  local repo_root="${REPO_ROOT:-$TOOL_MANIFEST_REPO_ROOT}"
  node "$repo_root/scripts/tool-manifest.js" field "$1" "$2"
}

tool_manifest_fields() {
  if [[ $# -eq 0 ]]; then
    echo 'tool_manifest_fields requires at least one TOOL.FIELD selector' >&2
    return 2
  fi
  local repo_root="${REPO_ROOT:-$TOOL_MANIFEST_REPO_ROOT}"
  node "$repo_root/scripts/tool-manifest.js" fields "$@"
}

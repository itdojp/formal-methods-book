#!/usr/bin/env bash
set -euo pipefail

tool="${1:-}"
case "$tool" in
  spin)
    sudo apt-get update
    sudo apt-get install --yes bison build-essential
    ;;
  nusmv)
    sudo apt-get update
    sudo apt-get install --yes \
      bison build-essential flex g++ gcc m4 patch pkg-config \
      python3 python3-venv xz-utils
    python3 -m venv tools/.tmp/nusmv-build-tools
    tools/.tmp/nusmv-build-tools/bin/pip install \
      --disable-pip-version-check \
      --require-hashes \
      --requirement tools/nusmv-build-requirements.txt
    echo "$GITHUB_WORKSPACE/tools/.tmp/nusmv-build-tools/bin" >> "$GITHUB_PATH"
    ;;
  kani)
    command -v rustup >/dev/null 2>&1 || {
      echo 'Kani optional lane requires rustup on the runner.' >&2
      exit 2
    }
    ;;
  alloy|tlc|apalache|dafny|cbmc|quint)
    ;;
  *)
    echo "Unsupported matrix tool: ${tool:-<missing>}" >&2
    exit 2
    ;;
esac

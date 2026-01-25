#!/usr/bin/env bash
set -euo pipefail

# Download pinned tool distributions into tools/.cache so that:
# - local runs are reproducible
# - CI can cache the directory and avoid re-downloading large artifacts

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE_DIR="$REPO_ROOT/tools/.cache"
TMP_DIR="$REPO_ROOT/tools/.tmp"

mkdir -p "$CACHE_DIR" "$TMP_DIR"

: "${ALLOY_VERSION:=6.2.0}"
: "${TLA_VERSION:=1.7.4}"
: "${APALACHE_VERSION:=0.52.1}"
: "${DAFNY_VERSION:=4.11.0}"

ALLOY_JAR="$CACHE_DIR/alloy-${ALLOY_VERSION}.jar"
TLA_JAR="$CACHE_DIR/tla2tools-${TLA_VERSION}.jar"
APALACHE_DIR="$CACHE_DIR/apalache-${APALACHE_VERSION}"
DAFNY_DIR="$CACHE_DIR/dafny-${DAFNY_VERSION}"

download() {
  local url="$1"
  local out="$2"
  if [[ -f "$out" ]]; then
    return 0
  fi
  echo "Downloading: $url"
  curl -fsSL --retry 3 --retry-delay 2 -L -o "$out" "$url"
}

ensure_alloy() {
  if [[ -f "$ALLOY_JAR" ]]; then
    return 0
  fi
  download \
    "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/org.alloytools.alloy.dist.jar" \
    "${ALLOY_JAR}.tmp"
  mv "${ALLOY_JAR}.tmp" "$ALLOY_JAR"
}

ensure_tla() {
  if [[ -f "$TLA_JAR" ]]; then
    return 0
  fi
  download \
    "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar" \
    "${TLA_JAR}.tmp"
  mv "${TLA_JAR}.tmp" "$TLA_JAR"
}

ensure_apalache() {
  if [[ -d "$APALACHE_DIR" ]]; then
    return 0
  fi
  local zip="$TMP_DIR/apalache-${APALACHE_VERSION}.zip"
  download \
    "https://github.com/apalache-mc/apalache/releases/download/v${APALACHE_VERSION}/apalache-${APALACHE_VERSION}.zip" \
    "$zip"

  rm -rf "$TMP_DIR/apalache-extract"
  mkdir -p "$TMP_DIR/apalache-extract"
  unzip -q "$zip" -d "$TMP_DIR/apalache-extract"
  mv "$TMP_DIR/apalache-extract/apalache-${APALACHE_VERSION}" "$APALACHE_DIR"
  rm -rf "$TMP_DIR/apalache-extract"
}

ensure_dafny() {
  if [[ -d "$DAFNY_DIR" ]]; then
    return 0
  fi
  local zip="$TMP_DIR/dafny-${DAFNY_VERSION}.zip"
  # Note: pin to ubuntu-22.04 x64 distribution for CI reproducibility.
  download \
    "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" \
    "$zip"

  rm -rf "$TMP_DIR/dafny-extract"
  mkdir -p "$TMP_DIR/dafny-extract"
  unzip -q "$zip" -d "$TMP_DIR/dafny-extract"
  mv "$TMP_DIR/dafny-extract/dafny" "$DAFNY_DIR"
  rm -rf "$TMP_DIR/dafny-extract"
}

ensure_alloy
ensure_tla
ensure_apalache
ensure_dafny

echo ""
echo "Installed tool set:"
echo "- Alloy:    ${ALLOY_VERSION} ($ALLOY_JAR)"
echo "- TLC:      ${TLA_VERSION} ($TLA_JAR)"
echo "- Apalache: ${APALACHE_VERSION} ($APALACHE_DIR)"
echo "- Dafny:    ${DAFNY_VERSION} ($DAFNY_DIR)"

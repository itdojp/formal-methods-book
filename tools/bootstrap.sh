#!/usr/bin/env bash
set -euo pipefail

# Download pinned tool distributions into tools/.cache so that:
# - local runs are reproducible
# - CI can cache the directory and avoid re-downloading large artifacts
#
# Notes:
# - Downloads are done atomically (via temp file + rename) to avoid reusing partial files.
# - For the default pinned versions, SHA-256 checksums are verified to reduce supply-chain risk.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE_DIR="$REPO_ROOT/tools/.cache"
TMP_DIR="$REPO_ROOT/tools/.tmp"

mkdir -p "$CACHE_DIR" "$TMP_DIR"

DEFAULT_ALLOY_VERSION="6.2.0"
DEFAULT_TLA_VERSION="1.7.4"
DEFAULT_APALACHE_VERSION="0.52.1"
DEFAULT_DAFNY_VERSION="4.11.0"

: "${ALLOY_VERSION:=$DEFAULT_ALLOY_VERSION}"
: "${TLA_VERSION:=$DEFAULT_TLA_VERSION}"
: "${APALACHE_VERSION:=$DEFAULT_APALACHE_VERSION}"
: "${DAFNY_VERSION:=$DEFAULT_DAFNY_VERSION}"

ALLOY_JAR="$CACHE_DIR/alloy-${ALLOY_VERSION}.jar"
TLA_JAR="$CACHE_DIR/tla2tools-${TLA_VERSION}.jar"
APALACHE_DIR="$CACHE_DIR/apalache-${APALACHE_VERSION}"
DAFNY_DIR="$CACHE_DIR/dafny-${DAFNY_VERSION}"

ALLOY_SHA256=""
TLA_SHA256=""
APALACHE_ZIP_SHA256=""
DAFNY_ZIP_SHA256=""

if [[ "$ALLOY_VERSION" == "$DEFAULT_ALLOY_VERSION" ]]; then
  ALLOY_SHA256="6b8c1cb5bc93bedfc7c61435c4e1ab6e688a242dc702a394628d9a9801edb78d"
fi
if [[ "$TLA_VERSION" == "$DEFAULT_TLA_VERSION" ]]; then
  TLA_SHA256="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
fi
if [[ "$APALACHE_VERSION" == "$DEFAULT_APALACHE_VERSION" ]]; then
  APALACHE_ZIP_SHA256="669ed18b5df000e05a37ab721f3227528aa6a82a038e5eee30b2b857bff6543f"
fi
if [[ "$DAFNY_VERSION" == "$DEFAULT_DAFNY_VERSION" ]]; then
  DAFNY_ZIP_SHA256="a46a9ff7cdd720f7955854c78e95df13f4cfe6b80691b05f8654fe19e8267179"
fi

sha256_of() {
  local file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$file" | awk '{print $1}'
    return 0
  fi
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$file" | awk '{print $1}'
    return 0
  fi
  if command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$file" | awk '{print $2}'
    return 0
  fi

  echo "No SHA-256 tool found (sha256sum/shasum/openssl)" >&2
  return 2
}

verify_sha256() {
  local expected="$1"
  local file="$2"
  local got=""
  got="$(sha256_of "$file")"
  if [[ "$got" != "$expected" ]]; then
    echo "Checksum mismatch: $file" >&2
    echo "  expected: $expected" >&2
    echo "  got:      $got" >&2
    return 1
  fi
}

download() {
  local url="$1"
  local out="$2"
  local expected_sha256="${3:-}"

  if [[ -f "$out" ]]; then
    if [[ -n "$expected_sha256" ]]; then
      if verify_sha256 "$expected_sha256" "$out"; then
        return 0
      fi
      echo "Re-downloading due to checksum mismatch: $out" >&2
      rm -f "$out"
    else
      # Best-effort sanity check when checksum is not available.
      if [[ -s "$out" ]]; then
        return 0
      fi
      rm -f "$out"
    fi
  fi

  local dir=""
  local tmp=""
  dir="$(dirname "$out")"
  tmp="$(mktemp "$dir/$(basename "$out").part.XXXXXX")"

  echo "Downloading: $url"
  if ! curl -fsSL --retry 3 --retry-delay 2 -L -o "$tmp" "$url"; then
    rm -f "$tmp"
    return 1
  fi

  if [[ ! -s "$tmp" ]]; then
    rm -f "$tmp"
    echo "Downloaded file is empty: $url" >&2
    return 1
  fi

  if [[ -n "$expected_sha256" ]]; then
    if ! verify_sha256 "$expected_sha256" "$tmp"; then
      rm -f "$tmp"
      return 1
    fi
  fi

  mv -f "$tmp" "$out"
}

ensure_alloy() {
  download \
    "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v${ALLOY_VERSION}/org.alloytools.alloy.dist.jar" \
    "$ALLOY_JAR" \
    "$ALLOY_SHA256"
}

ensure_tla() {
  download \
    "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar" \
    "$TLA_JAR" \
    "$TLA_SHA256"
}

ensure_apalache() {
  local bin="$APALACHE_DIR/bin/apalache-mc"
  if [[ -d "$APALACHE_DIR" && -x "$bin" ]]; then
    return 0
  fi
  rm -rf "$APALACHE_DIR"

  local zip="$TMP_DIR/apalache-${APALACHE_VERSION}.zip"
  download \
    "https://github.com/apalache-mc/apalache/releases/download/v${APALACHE_VERSION}/apalache-${APALACHE_VERSION}.zip" \
    "$zip" \
    "$APALACHE_ZIP_SHA256"

  rm -rf "$TMP_DIR/apalache-extract"
  mkdir -p "$TMP_DIR/apalache-extract"
  unzip -q "$zip" -d "$TMP_DIR/apalache-extract"
  mv "$TMP_DIR/apalache-extract/apalache-${APALACHE_VERSION}" "$APALACHE_DIR"
  rm -rf "$TMP_DIR/apalache-extract"
}

ensure_dafny() {
  local bin="$DAFNY_DIR/DafnyDriver"
  if [[ -d "$DAFNY_DIR" && -x "$bin" ]]; then
    return 0
  fi
  rm -rf "$DAFNY_DIR"

  local zip="$TMP_DIR/dafny-${DAFNY_VERSION}.zip"
  # Note: pin to ubuntu-22.04 x64 distribution for CI reproducibility.
  download \
    "https://github.com/dafny-lang/dafny/releases/download/v${DAFNY_VERSION}/dafny-${DAFNY_VERSION}-x64-ubuntu-22.04.zip" \
    "$zip" \
    "$DAFNY_ZIP_SHA256"

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


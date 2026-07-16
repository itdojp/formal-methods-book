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
source "$REPO_ROOT/tools/lib/tool-manifest.sh"

mkdir -p "$CACHE_DIR" "$TMP_DIR"

ALLOY_VERSION="$(tool_manifest_field alloy version)"
TLA_VERSION="$(tool_manifest_field tlc version)"
APALACHE_VERSION="$(tool_manifest_field apalache version)"
DAFNY_VERSION="$(tool_manifest_field dafny version)"
SPIN_VERSION="$(tool_manifest_field spin version)"
SPIN_COMMIT="$(tool_manifest_field spin commit)"
NUSMV_VERSION="$(tool_manifest_field nusmv version)"
CBMC_VERSION="$(tool_manifest_field cbmc version)"
QUINT_VERSION="$(tool_manifest_field quint version)"
KANI_VERSION="$(tool_manifest_field kani version)"
KANI_RUST_TOOLCHAIN="$(tool_manifest_field kani rustToolchain)"

ALLOY_URL="$(tool_manifest_field alloy distribution.url)"
TLA_URL="$(tool_manifest_field tlc distribution.url)"
APALACHE_URL="$(tool_manifest_field apalache distribution.url)"
DAFNY_URL="$(tool_manifest_field dafny distribution.url)"
SPIN_URL="$(tool_manifest_field spin distribution.url)"
NUSMV_URL="$(tool_manifest_field nusmv distribution.url)"
CBMC_URL="$(tool_manifest_field cbmc distribution.url)"
QUINT_URL="$(tool_manifest_field quint distribution.url)"
KANI_URL="$(tool_manifest_field kani distribution.url)"

ALLOY_SHA256="$(tool_manifest_field alloy distribution.sha256)"
TLA_SHA256="$(tool_manifest_field tlc distribution.sha256)"
APALACHE_ZIP_SHA256="$(tool_manifest_field apalache distribution.sha256)"
DAFNY_ZIP_SHA256="$(tool_manifest_field dafny distribution.sha256)"
SPIN_TAR_SHA256="$(tool_manifest_field spin distribution.sha256)"
NUSMV_TAR_SHA256="$(tool_manifest_field nusmv distribution.sha256)"
CBMC_DEB_SHA256="$(tool_manifest_field cbmc distribution.sha256)"
QUINT_SHA256="$(tool_manifest_field quint distribution.sha256)"
KANI_TAR_SHA256="$(tool_manifest_field kani distribution.sha256)"

ALLOY_JAR="$CACHE_DIR/alloy-${ALLOY_VERSION}.jar"
TLA_JAR="$CACHE_DIR/tla2tools-${TLA_VERSION}.jar"
APALACHE_DIR="$CACHE_DIR/apalache-${APALACHE_VERSION}"
DAFNY_DIR="$CACHE_DIR/dafny-${DAFNY_VERSION}"
SPIN_DIR="$CACHE_DIR/spin-${SPIN_VERSION}"
NUSMV_DIR="$CACHE_DIR/nusmv-${NUSMV_VERSION}"
CBMC_DIR="$CACHE_DIR/cbmc-${CBMC_VERSION}"
QUINT_BIN="$CACHE_DIR/quint-${QUINT_VERSION}/quint"
KANI_DIR="$CACHE_DIR/kani-${KANI_VERSION}"
KANI_RUSTUP_HOME="$CACHE_DIR/kani-rustup-${KANI_RUST_TOOLCHAIN}"
KANI_CARGO_HOME="$CACHE_DIR/kani-cargo"

usage() {
  cat <<'EOF'
Usage:
  tools/bootstrap.sh [--lane pr-quick|nightly|optional]
  tools/bootstrap.sh --tool TOOL [--tool ...]

Without arguments, only the pr-quick tools are installed. Nightly tools are
never downloaded or built by the default/PR path.
EOF
}

selected_lane=""
selected_tools=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --lane)
      if [[ $# -lt 2 || "$2" == -* ]]; then
        echo "Missing value for --lane" >&2
        usage >&2
        exit 2
      fi
      selected_lane="$2"
      shift 2
      ;;
    --tool)
      if [[ $# -lt 2 || "$2" == -* ]]; then
        echo "Missing value for --tool" >&2
        usage >&2
        exit 2
      fi
      selected_tools+=("$2")
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ -n "$selected_lane" && ${#selected_tools[@]} -gt 0 ]]; then
  echo "Use either --lane or --tool, not both" >&2
  exit 2
fi
if [[ -z "$selected_lane" && ${#selected_tools[@]} -eq 0 ]]; then
  selected_lane="pr-quick"
fi
if [[ -n "$selected_lane" ]]; then
  selected_output=""
  if ! selected_output="$(node "$REPO_ROOT/scripts/tool-manifest.js" tools --lane "$selected_lane")"; then
    echo "Unknown or empty executable lane: $selected_lane" >&2
    usage >&2
    exit 2
  fi
  mapfile -t selected_tools <<< "$selected_output"
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
  if ! curl -fsSL --retry 3 --retry-delay 2 -o "$tmp" "$url"; then
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
    "$ALLOY_URL" \
    "$ALLOY_JAR" \
    "$ALLOY_SHA256"
}

ensure_tla() {
  download \
    "$TLA_URL" \
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
    "$APALACHE_URL" \
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
    "$DAFNY_URL" \
    "$zip" \
    "$DAFNY_ZIP_SHA256"

  rm -rf "$TMP_DIR/dafny-extract"
  mkdir -p "$TMP_DIR/dafny-extract"
  unzip -q "$zip" -d "$TMP_DIR/dafny-extract"
  mv "$TMP_DIR/dafny-extract/dafny" "$DAFNY_DIR"
  rm -rf "$TMP_DIR/dafny-extract"
}

require_command() {
  local command_name="$1"
  local package_hint="$2"
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "Required command not found: $command_name (install $package_hint)" >&2
    return 2
  fi
}

ensure_spin() {
  local bin="$SPIN_DIR/bin/spin"
  local commit_file="$SPIN_DIR/commit.txt"
  local cached_commit=""
  if [[ -f "$commit_file" ]]; then
    IFS= read -r cached_commit < "$commit_file" || true
  fi
  if [[ -x "$bin" && "$cached_commit" == "$SPIN_COMMIT" ]]; then
    return 0
  fi
  require_command cc build-essential
  require_command make build-essential
  require_command bison bison

  local archive="$TMP_DIR/spin-${SPIN_COMMIT}.tar.gz"
  download \
    "$SPIN_URL" \
    "$archive" \
    "$SPIN_TAR_SHA256"

  local source_dir="$TMP_DIR/spin-${SPIN_COMMIT}-source"
  rm -rf "$source_dir" "$SPIN_DIR"
  mkdir -p "$source_dir" "$SPIN_DIR/bin"
  tar -xzf "$archive" -C "$source_dir" --strip-components=1
  LC_ALL=C make -C "$source_dir/Src" -j2 YACC='bison -y'
  install -m 0755 "$source_dir/Src/spin" "$bin"
  printf '%s\n' "$SPIN_COMMIT" > "$SPIN_DIR/commit.txt"
  rm -rf "$source_dir"
}

ensure_nusmv() {
  local bin="$NUSMV_DIR/bin/NuSMV"
  if [[ -x "$bin" ]]; then
    return 0
  fi
  require_command gcc build-essential
  require_command g++ build-essential
  require_command flex flex
  require_command bison bison
  require_command m4 m4
  require_command patch patch
  require_command python3 python3
  require_command meson 'meson >= 1.5'
  require_command ninja ninja-build
  require_command pkg-config pkg-config

  local meson_version=""
  meson_version="$(meson --version)"
  if ! python3 - "$meson_version" <<'PY'
import sys
parts = tuple(int(part) for part in sys.argv[1].split('.')[:2])
raise SystemExit(0 if parts >= (1, 5) else 1)
PY
  then
    echo "NuSMV ${NUSMV_VERSION} requires meson >= 1.5 (found ${meson_version})" >&2
    return 2
  fi

  local archive="$TMP_DIR/NuSMV-${NUSMV_VERSION}.tar.xz"
  download \
    "$NUSMV_URL" \
    "$archive" \
    "$NUSMV_TAR_SHA256"

  local source_dir="$TMP_DIR/nusmv-${NUSMV_VERSION}-source"
  local build_dir="$TMP_DIR/nusmv-${NUSMV_VERSION}-build"
  local install_dir="$NUSMV_DIR"
  rm -rf "$source_dir" "$build_dir" "$install_dir"
  mkdir -p "$source_dir" "$build_dir" "$install_dir"
  tar -xJf "$archive" -C "$source_dir" --strip-components=1

  # Release builds embed the current date by default. Make that value derive
  # from the checksummed source archive instead of the CI clock.
  export SOURCE_DATE_EPOCH
  SOURCE_DATE_EPOCH="$(stat -c %Y "$source_dir/meson.build")"
  python3 - "$source_dir/code/meson.build" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding='utf-8')
old = "'import time; print(time.asctime())'"
new = "'import os, time; print(time.asctime(time.gmtime(int(os.environ[\"SOURCE_DATE_EPOCH\"]))))'"
if text.count(old) != 1:
    raise SystemExit('NuSMV build-date patch target was not found exactly once')
path.write_text(text.replace(old, new), encoding='utf-8')
PY

  # NuSMV's shell depends on libedit. The executable examples only need batch
  # mode, so disable the shell rather than linking or symlinking libedit.so.0.
  LC_ALL=C meson setup "$build_dir" "$source_dir" \
    --buildtype=release \
    --prefix="$install_dir" \
    --wrap-mode=nodownload \
    -Dbuild-doc=disabled \
    -Dwith-bignumbers=disabled \
    -Dwith-compass=disabled \
    -Dwith-gtest=disabled \
    -Dwith-libxml2=disabled \
    -Dwith-ltl2smv=disabled \
    -Dwith-minisat=disabled \
    -Dwith-profiler=disabled \
    -Dwith-shell=disabled \
    -Dwith-watchdog=disabled \
    -Ddata-dir="$install_dir/share"
  LC_ALL=C meson compile -C "$build_dir" -j2
  LC_ALL=C meson install -C "$build_dir"
  if [[ ! -x "$bin" ]]; then
    echo "NuSMV build completed but executable was not installed at $bin" >&2
    return 1
  fi
  rm -rf "$source_dir" "$build_dir"
}

ensure_cbmc() {
  local bin="$CBMC_DIR/usr/bin/cbmc"
  if [[ -x "$bin" ]]; then
    return 0
  fi
  require_command dpkg-deb dpkg

  local deb="$TMP_DIR/ubuntu-24.04-cbmc-${CBMC_VERSION}-Linux.deb"
  download \
    "$CBMC_URL" \
    "$deb" \
    "$CBMC_DEB_SHA256"
  rm -rf "$CBMC_DIR"
  mkdir -p "$CBMC_DIR"
  dpkg-deb -x "$deb" "$CBMC_DIR"
  if [[ ! -x "$bin" ]]; then
    echo "CBMC package did not contain expected executable: $bin" >&2
    return 1
  fi
}

ensure_quint() {
  if [[ -x "$QUINT_BIN" ]]; then
    return 0
  fi
  mkdir -p "$(dirname "$QUINT_BIN")"
  download "$QUINT_URL" "$QUINT_BIN" "$QUINT_SHA256"
  chmod 0755 "$QUINT_BIN"
  if [[ "$($QUINT_BIN --version)" != "$QUINT_VERSION" ]]; then
    echo "Quint binary version did not match manifest: $QUINT_VERSION" >&2
    return 1
  fi
}

ensure_kani() {
  local bin="$KANI_DIR/bin/kani-driver"
  local archive="$TMP_DIR/kani-${KANI_VERSION}-x86_64-unknown-linux-gnu.tar.gz"
  require_command rustup rustup
  require_command tar tar

  if [[ ! -x "$bin" ]]; then
    download "$KANI_URL" "$archive" "$KANI_TAR_SHA256"
    local extract_dir="$TMP_DIR/kani-${KANI_VERSION}-extract"
    rm -rf "$extract_dir" "$KANI_DIR"
    mkdir -p "$extract_dir" "$KANI_DIR"
    tar -xzf "$archive" -C "$extract_dir" --strip-components=1
    mv "$extract_dir"/* "$KANI_DIR"/
    rmdir "$extract_dir"
  fi

  mkdir -p "$KANI_RUSTUP_HOME" "$KANI_CARGO_HOME"
  RUSTUP_HOME="$KANI_RUSTUP_HOME" CARGO_HOME="$KANI_CARGO_HOME" \
    rustup toolchain install "$KANI_RUST_TOOLCHAIN" --profile minimal --no-self-update

  if [[ "$($bin --version)" != "kani $KANI_VERSION" ]]; then
    echo "Kani binary version did not match manifest: $KANI_VERSION" >&2
    return 1
  fi
}

installed=()
for selected_tool in "${selected_tools[@]}"; do
  case "$selected_tool" in
    alloy) ensure_alloy; installed+=("Alloy ${ALLOY_VERSION}") ;;
    tlc) ensure_tla; installed+=("TLC ${TLA_VERSION}") ;;
    apalache) ensure_apalache; installed+=("Apalache ${APALACHE_VERSION}") ;;
    dafny) ensure_dafny; installed+=("Dafny ${DAFNY_VERSION}") ;;
    spin) ensure_spin; installed+=("SPIN ${SPIN_VERSION} (${SPIN_COMMIT})") ;;
    nusmv) ensure_nusmv; installed+=("NuSMV ${NUSMV_VERSION} (official LGPL source)") ;;
    cbmc) ensure_cbmc; installed+=("CBMC ${CBMC_VERSION}") ;;
    quint) ensure_quint; installed+=("Quint ${QUINT_VERSION}") ;;
    kani) ensure_kani; installed+=("Kani ${KANI_VERSION} (${KANI_RUST_TOOLCHAIN})") ;;
    *)
      echo "Unknown tool: $selected_tool" >&2
      usage >&2
      exit 2
      ;;
  esac
done

echo ""
echo "Installed tool set:"
printf -- '- %s\n' "${installed[@]}"

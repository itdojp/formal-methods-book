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

manifest_output="$(tool_manifest_fields \
  alloy.version tlc.version apalache.version dafny.version spin.version \
  spin.commit nusmv.version cbmc.version quint.version prism.version tamarin.version kani.version \
  tamarin.commit tamarin.maudeVersion tamarin.maudeCommit \
  kani.rustToolchain kani.rustToolchainManifest.url kani.rustToolchainManifest.sha256 \
  alloy.distribution.url tlc.distribution.url apalache.distribution.url \
  dafny.distribution.url spin.distribution.url nusmv.distribution.url \
  cbmc.distribution.url quint.distribution.url prism.distribution.url \
  tamarin.distribution.url tamarin.maudeDistribution.url kani.distribution.url \
  alloy.distribution.sha256 tlc.distribution.sha256 apalache.distribution.sha256 \
  dafny.distribution.sha256 spin.distribution.sha256 nusmv.distribution.sha256 \
  cbmc.distribution.sha256 quint.distribution.sha256 prism.distribution.sha256 \
  tamarin.distribution.sha256 tamarin.maudeDistribution.sha256 kani.distribution.sha256)"
mapfile -t manifest_values <<< "$manifest_output"
if [[ ${#manifest_values[@]} -ne 42 ]]; then
  echo "Unexpected bootstrap field count: ${#manifest_values[@]} (expected 42)" >&2
  exit 2
fi
manifest_index=0
next_manifest_value() {
  printf -v "$1" '%s' "${manifest_values[$manifest_index]}"
  manifest_index=$((manifest_index + 1))
}

next_manifest_value ALLOY_VERSION
next_manifest_value TLA_VERSION
next_manifest_value APALACHE_VERSION
next_manifest_value DAFNY_VERSION
next_manifest_value SPIN_VERSION
next_manifest_value SPIN_COMMIT
next_manifest_value NUSMV_VERSION
next_manifest_value CBMC_VERSION
next_manifest_value QUINT_VERSION
next_manifest_value PRISM_VERSION
next_manifest_value TAMARIN_VERSION
next_manifest_value KANI_VERSION
next_manifest_value TAMARIN_COMMIT
next_manifest_value TAMARIN_MAUDE_VERSION
next_manifest_value TAMARIN_MAUDE_COMMIT
next_manifest_value KANI_RUST_TOOLCHAIN
next_manifest_value KANI_RUST_MANIFEST_URL
next_manifest_value KANI_RUST_MANIFEST_SHA256
next_manifest_value ALLOY_URL
next_manifest_value TLA_URL
next_manifest_value APALACHE_URL
next_manifest_value DAFNY_URL
next_manifest_value SPIN_URL
next_manifest_value NUSMV_URL
next_manifest_value CBMC_URL
next_manifest_value QUINT_URL
next_manifest_value PRISM_URL
next_manifest_value TAMARIN_URL
next_manifest_value TAMARIN_MAUDE_URL
next_manifest_value KANI_URL
next_manifest_value ALLOY_SHA256
next_manifest_value TLA_SHA256
next_manifest_value APALACHE_ZIP_SHA256
next_manifest_value DAFNY_ZIP_SHA256
next_manifest_value SPIN_TAR_SHA256
next_manifest_value NUSMV_TAR_SHA256
next_manifest_value CBMC_DEB_SHA256
next_manifest_value QUINT_SHA256
next_manifest_value PRISM_TAR_SHA256
next_manifest_value TAMARIN_TAR_SHA256
next_manifest_value TAMARIN_MAUDE_ZIP_SHA256
next_manifest_value KANI_TAR_SHA256
unset manifest_output manifest_values manifest_index

ALLOY_JAR="$CACHE_DIR/alloy-${ALLOY_VERSION}.jar"
TLA_JAR="$CACHE_DIR/tla2tools-${TLA_VERSION}.jar"
APALACHE_DIR="$CACHE_DIR/apalache-${APALACHE_VERSION}"
DAFNY_DIR="$CACHE_DIR/dafny-${DAFNY_VERSION}"
SPIN_DIR="$CACHE_DIR/spin-${SPIN_VERSION}"
NUSMV_DIR="$CACHE_DIR/nusmv-${NUSMV_VERSION}"
CBMC_DIR="$CACHE_DIR/cbmc-${CBMC_VERSION}"
QUINT_BIN="$CACHE_DIR/quint-${QUINT_VERSION}/quint"
PRISM_DIR="$CACHE_DIR/prism-${PRISM_VERSION}"
TAMARIN_DIR="$CACHE_DIR/tamarin-${TAMARIN_VERSION}"
TAMARIN_BIN="$TAMARIN_DIR/tamarin-prover"
TAMARIN_MAUDE_DIR="$CACHE_DIR/maude-${TAMARIN_MAUDE_VERSION}"
TAMARIN_MAUDE_BIN="$TAMARIN_MAUDE_DIR/maude"
KANI_DIR="$CACHE_DIR/kani-${KANI_VERSION}"
KANI_RUSTUP_HOME="$CACHE_DIR/kani-rustup-${KANI_RUST_TOOLCHAIN}"
KANI_CARGO_HOME="$CACHE_DIR/kani-cargo"
KANI_ARCHIVE="$CACHE_DIR/downloads/kani-${KANI_VERSION}-x86_64-unknown-linux-gnu.tar.gz"
PRISM_ARCHIVE="$CACHE_DIR/downloads/prism-${PRISM_VERSION}-linux64-x86.tar.gz"
TAMARIN_ARCHIVE="$CACHE_DIR/downloads/tamarin-prover-${TAMARIN_VERSION}-linux64-ubuntu.tar.gz"
TAMARIN_MAUDE_ARCHIVE="$CACHE_DIR/downloads/maude-${TAMARIN_MAUDE_VERSION}-linux-x86_64.zip"
KANI_RUST_MANIFEST="$CACHE_DIR/downloads/$(basename "$KANI_RUST_MANIFEST_URL")"

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
  mkdir -p "$(dirname "$QUINT_BIN")"
  # download() verifies an existing cached file before reuse.
  download "$QUINT_URL" "$QUINT_BIN" "$QUINT_SHA256"
  chmod 0755 "$QUINT_BIN"
  if [[ "$($QUINT_BIN --version)" != "$QUINT_VERSION" ]]; then
    echo "Quint binary version did not match manifest: $QUINT_VERSION" >&2
    return 1
  fi
}

ensure_prism() {
  local bin="$PRISM_DIR/bin/prism"
  require_command tar tar

  mkdir -p "$(dirname "$PRISM_ARCHIVE")"
  # Cache the checksum-verified archive, but re-extract it for every bootstrap.
  # PRISM's install script writes an absolute path into its launchers, so this
  # also prevents a restored cache from retaining a path from another runner.
  download "$PRISM_URL" "$PRISM_ARCHIVE" "$PRISM_TAR_SHA256"

  local extract_dir="$TMP_DIR/prism-${PRISM_VERSION}-extract"
  local extracted_root="$extract_dir/prism-${PRISM_VERSION}-linux64-x86"
  rm -rf "$extract_dir" "$PRISM_DIR"
  mkdir -p "$extract_dir"
  tar -xzf "$PRISM_ARCHIVE" -C "$extract_dir"
  if [[ ! -x "$extracted_root/install.sh" || ! -x "$extracted_root/bin/prism" ]]; then
    echo "PRISM archive did not contain the expected Linux x86-64 layout" >&2
    return 1
  fi
  mv "$extracted_root" "$PRISM_DIR"
  rmdir "$extract_dir"
  (cd "$PRISM_DIR" && ./install.sh silent)
  if [[ "$($bin -version)" != "PRISM version $PRISM_VERSION" ]]; then
    echo "PRISM binary version did not match manifest: $PRISM_VERSION" >&2
    return 1
  fi
}

ensure_tamarin() {
  require_command tar tar
  require_command unzip unzip
  mkdir -p "$(dirname "$TAMARIN_ARCHIVE")"

  # Keep only checksum-verified archives in the reusable cache. Re-extract on
  # every bootstrap so a modified executable cannot survive a cache restore.
  download "$TAMARIN_URL" "$TAMARIN_ARCHIVE" "$TAMARIN_TAR_SHA256"
  download "$TAMARIN_MAUDE_URL" "$TAMARIN_MAUDE_ARCHIVE" "$TAMARIN_MAUDE_ZIP_SHA256"

  local tamarin_entries=""
  tamarin_entries="$(tar -tzf "$TAMARIN_ARCHIVE")"
  if [[ "$tamarin_entries" != 'tamarin-prover' ]]; then
    echo 'Tamarin archive did not contain the expected single-file layout' >&2
    return 1
  fi

  local maude_entry=""
  while IFS= read -r maude_entry; do
    if [[ -z "$maude_entry" || ! "$maude_entry" =~ ^[A-Za-z0-9._-]+$ \
        || "$maude_entry" == .* ]]; then
      echo "Maude archive contained an unsafe path: ${maude_entry:-<empty>}" >&2
      return 1
    fi
  done < <(unzip -Z1 "$TAMARIN_MAUDE_ARCHIVE")
  if ! unzip -Z1 "$TAMARIN_MAUDE_ARCHIVE" | grep -Fxq 'maude' \
      || ! unzip -Z1 "$TAMARIN_MAUDE_ARCHIVE" | grep -Fxq 'prelude.maude'; then
    echo 'Maude archive did not contain maude and prelude.maude' >&2
    return 1
  fi
  if [[ -n "$(unzip -Z1 "$TAMARIN_MAUDE_ARCHIVE" | sort | uniq -d)" ]]; then
    echo 'Maude archive contained duplicate entries' >&2
    return 1
  fi

  rm -rf "$TAMARIN_DIR" "$TAMARIN_MAUDE_DIR"
  mkdir -p "$TAMARIN_DIR" "$TAMARIN_MAUDE_DIR"
  tar -xzf "$TAMARIN_ARCHIVE" -C "$TAMARIN_DIR"
  unzip -q "$TAMARIN_MAUDE_ARCHIVE" -d "$TAMARIN_MAUDE_DIR"
  if [[ ! -x "$TAMARIN_BIN" || ! -x "$TAMARIN_MAUDE_BIN" \
      || ! -f "$TAMARIN_MAUDE_DIR/prelude.maude" \
      || -L "$TAMARIN_BIN" || -L "$TAMARIN_MAUDE_BIN" \
      || -n "$(find "$TAMARIN_MAUDE_DIR" -type l -print -quit)" ]]; then
    echo 'Tamarin or Maude archive did not contain the expected executable layout' >&2
    return 1
  fi
  if [[ "$($TAMARIN_MAUDE_BIN --version)" != "$TAMARIN_MAUDE_VERSION" ]]; then
    echo "Maude binary version did not match manifest: $TAMARIN_MAUDE_VERSION" >&2
    return 1
  fi

  local version_output=""
  version_output="$("$TAMARIN_BIN" --with-maude="$TAMARIN_MAUDE_BIN" --version 2>&1)"
  if ! grep -Fq "Tamarin version $TAMARIN_VERSION" <<< "$version_output" \
      || ! grep -Fq "Maude version $TAMARIN_MAUDE_VERSION" <<< "$version_output" \
      || ! grep -Fq "Git revision: $TAMARIN_COMMIT" <<< "$version_output"; then
    echo 'Tamarin/Maude binary provenance did not match the manifest' >&2
    printf '%s\n' "$version_output" >&2
    return 1
  fi
}

ensure_kani() {
  local bin="$KANI_DIR/bin/kani-driver"
  require_command rustup rustup
  require_command tar tar

  mkdir -p "$(dirname "$KANI_ARCHIVE")"
  # Cache the checksummed archive, but never trust a restored extracted tree.
  # Re-extraction after verifying the archive prevents cache poisoning from
  # replacing kani-driver or one of its bundled helper binaries.
  download "$KANI_URL" "$KANI_ARCHIVE" "$KANI_TAR_SHA256"
  local extract_dir="$TMP_DIR/kani-${KANI_VERSION}-extract"
  rm -rf "$extract_dir" "$KANI_DIR"
  mkdir -p "$extract_dir" "$KANI_DIR"
  tar -xzf "$KANI_ARCHIVE" -C "$extract_dir" --strip-components=1
  mv "$extract_dir"/* "$KANI_DIR"/
  rmdir "$extract_dir"

  # Pin and verify the dated Rust channel manifest. rustup then verifies each
  # component against the checksums in this upstream manifest.
  download "$KANI_RUST_MANIFEST_URL" "$KANI_RUST_MANIFEST" "$KANI_RUST_MANIFEST_SHA256"

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
    prism) ensure_prism; installed+=("PRISM ${PRISM_VERSION}") ;;
    tamarin) ensure_tamarin; installed+=("Tamarin ${TAMARIN_VERSION} (Maude ${TAMARIN_MAUDE_VERSION})") ;;
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

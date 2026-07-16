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
  spin.commit nusmv.version cbmc.version quint.version prism.version tamarin.version sby.version kani.version \
  cvc5.version cvc5.commit cvc5.checkerVersion cvc5.checkerCommit cvc5.certificateFormat cvc5.maxCertificateBytes \
  cvc5.maxCheckerOutputBytes cvc5.rustToolchain cvc5.rustcCommit cvc5.cargoCommit cvc5.rustHost \
  cvc5.rustToolchainManifest.url cvc5.rustToolchainManifest.sha256 cvc5.checkerCargoLockSha256 \
  rtlola.version rtlola.commit rtlola.cargoLockSha256 rtlola.rustToolchain rtlola.rustcCommit rtlola.cargoCommit rtlola.rustHost \
  rtlola.rustToolchainManifest.url rtlola.rustToolchainManifest.sha256 \
  tamarin.commit tamarin.maudeVersion tamarin.maudeCommit \
  sby.commit sby.suiteVersion sby.suiteCommit sby.yosysVersion sby.yosysCommit sby.bitwuzlaVersion sby.bitwuzlaCommit \
  kani.rustToolchain kani.rustToolchainManifest.url kani.rustToolchainManifest.sha256 \
  alloy.distribution.url tlc.distribution.url apalache.distribution.url \
  dafny.distribution.url spin.distribution.url nusmv.distribution.url \
  cbmc.distribution.url quint.distribution.url prism.distribution.url \
  tamarin.distribution.url tamarin.maudeDistribution.url sby.distribution.url kani.distribution.url \
  cvc5.distribution.url cvc5.checkerDistribution.url rtlola.distribution.url \
  alloy.distribution.sha256 tlc.distribution.sha256 apalache.distribution.sha256 \
  dafny.distribution.sha256 spin.distribution.sha256 nusmv.distribution.sha256 \
  cbmc.distribution.sha256 quint.distribution.sha256 prism.distribution.sha256 \
  tamarin.distribution.sha256 tamarin.maudeDistribution.sha256 sby.distribution.sha256 kani.distribution.sha256 \
  cvc5.distribution.sha256 cvc5.checkerDistribution.sha256 rtlola.distribution.sha256)"
mapfile -t manifest_values <<< "$manifest_output"
if [[ ${#manifest_values[@]} -ne 81 ]]; then
  echo "Unexpected bootstrap field count: ${#manifest_values[@]} (expected 81)" >&2
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
next_manifest_value SBY_VERSION
next_manifest_value KANI_VERSION
next_manifest_value CVC5_VERSION
next_manifest_value CVC5_COMMIT
next_manifest_value CARCARA_VERSION
next_manifest_value CARCARA_COMMIT
next_manifest_value CVC5_CERTIFICATE_FORMAT
next_manifest_value CVC5_MAX_CERTIFICATE_BYTES
next_manifest_value CARCARA_MAX_CHECKER_OUTPUT_BYTES
next_manifest_value CARCARA_RUST_TOOLCHAIN
next_manifest_value CARCARA_RUSTC_COMMIT
next_manifest_value CARCARA_CARGO_COMMIT
next_manifest_value CARCARA_RUST_HOST
next_manifest_value CARCARA_RUST_MANIFEST_URL
next_manifest_value CARCARA_RUST_MANIFEST_SHA256
next_manifest_value CARCARA_CARGO_LOCK_SHA256
next_manifest_value RTLOLA_VERSION
next_manifest_value RTLOLA_COMMIT
next_manifest_value RTLOLA_CARGO_LOCK_SHA256
next_manifest_value RTLOLA_RUST_TOOLCHAIN
next_manifest_value RTLOLA_RUSTC_COMMIT
next_manifest_value RTLOLA_CARGO_COMMIT
next_manifest_value RTLOLA_RUST_HOST
next_manifest_value RTLOLA_RUST_MANIFEST_URL
next_manifest_value RTLOLA_RUST_MANIFEST_SHA256
next_manifest_value TAMARIN_COMMIT
next_manifest_value TAMARIN_MAUDE_VERSION
next_manifest_value TAMARIN_MAUDE_COMMIT
next_manifest_value SBY_COMMIT
next_manifest_value SBY_SUITE_VERSION
next_manifest_value SBY_SUITE_COMMIT
next_manifest_value SBY_YOSYS_VERSION
next_manifest_value SBY_YOSYS_COMMIT
next_manifest_value SBY_BITWUZLA_VERSION
next_manifest_value SBY_BITWUZLA_COMMIT
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
next_manifest_value SBY_URL
next_manifest_value KANI_URL
next_manifest_value CVC5_URL
next_manifest_value CARCARA_URL
next_manifest_value RTLOLA_URL
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
next_manifest_value SBY_TAR_SHA256
next_manifest_value KANI_TAR_SHA256
next_manifest_value CVC5_ZIP_SHA256
next_manifest_value CARCARA_TAR_SHA256
next_manifest_value RTLOLA_CRATE_SHA256
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
SBY_SUITE_DIR="$TMP_DIR/oss-cad-suite-${SBY_SUITE_VERSION}"
TAMARIN_MAUDE_BIN="$TAMARIN_MAUDE_DIR/maude"
KANI_DIR="$CACHE_DIR/kani-${KANI_VERSION}"
KANI_RUSTUP_HOME="$CACHE_DIR/kani-rustup-${KANI_RUST_TOOLCHAIN}"
KANI_CARGO_HOME="$CACHE_DIR/kani-cargo"
CVC5_DIR="$CACHE_DIR/cvc5-${CVC5_VERSION}"
CVC5_BIN="$CVC5_DIR/bin/cvc5"
CARCARA_DIR="$TMP_DIR/carcara-${CARCARA_VERSION}"
CARCARA_BIN="$CARCARA_DIR/target/release/carcara"
CARCARA_RUSTUP_HOME="$CACHE_DIR/carcara-rustup-${CARCARA_RUST_TOOLCHAIN}"
CARCARA_CARGO_HOME="$CACHE_DIR/carcara-cargo"
RTLOLA_DIR="$TMP_DIR/rtlola-$RTLOLA_VERSION"
RTLOLA_BIN="$RTLOLA_DIR/target/release/rtlola-cli"
RTLOLA_RUSTUP_HOME="$CACHE_DIR/rtlola-rustup-$RTLOLA_RUST_TOOLCHAIN"
RTLOLA_CARGO_HOME="$CACHE_DIR/rtlola-cargo"
KANI_ARCHIVE="$CACHE_DIR/downloads/kani-${KANI_VERSION}-x86_64-unknown-linux-gnu.tar.gz"
PRISM_ARCHIVE="$CACHE_DIR/downloads/prism-${PRISM_VERSION}-linux64-x86.tar.gz"
TAMARIN_ARCHIVE="$CACHE_DIR/downloads/tamarin-prover-${TAMARIN_VERSION}-linux64-ubuntu.tar.gz"
TAMARIN_MAUDE_ARCHIVE="$CACHE_DIR/downloads/maude-${TAMARIN_MAUDE_VERSION}-linux-x86_64.zip"
SBY_ARCHIVE="$CACHE_DIR/downloads/oss-cad-suite-linux-x64-${SBY_SUITE_VERSION}.tgz"
KANI_RUST_MANIFEST="$CACHE_DIR/downloads/$(basename "$KANI_RUST_MANIFEST_URL")"
CVC5_ARCHIVE="$CACHE_DIR/downloads/cvc5-Linux-x86_64-static.zip"
CARCARA_ARCHIVE="$CACHE_DIR/downloads/carcara-${CARCARA_COMMIT}.tar.gz"
CARCARA_RUST_MANIFEST="$CACHE_DIR/downloads/$(basename "$CARCARA_RUST_MANIFEST_URL")"
RTLOLA_ARCHIVE="$CACHE_DIR/downloads/rtlola-cli-$RTLOLA_VERSION.crate"
RTLOLA_RUST_MANIFEST="$CACHE_DIR/downloads/rtlola-$(basename "$RTLOLA_RUST_MANIFEST_URL")"

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

safe_extract_archive() {
  local archive="$1"
  local archive_kind="$2"
  local destination="$3"
  local expected_root="$4"
  require_command python3 python3
  rm -rf "$destination"
  mkdir -p "$destination"
  python3 - "$archive" "$archive_kind" "$destination" "$expected_root" <<'PYTHON'
import os
import posixpath
import shutil
import stat
import sys
import tarfile
import zipfile
from pathlib import Path

archive, kind, destination, expected_root = sys.argv[1:]
destination = Path(destination)
max_members = 4096
max_member_bytes = 256 * 1024 * 1024
max_total_bytes = 512 * 1024 * 1024

def unsafe(name):
    return (not name or name.startswith('/') or '\\' in name or
            posixpath.normpath(name) != name or name == '..' or name.startswith('../'))

def validate_name(name, seen):
    normalized = name.rstrip('/')
    if unsafe(normalized) or not (normalized == expected_root or normalized.startswith(expected_root + '/')):
        raise SystemExit(f'Unsafe {kind} archive path: {name!r}')
    if normalized in seen:
        raise SystemExit(f'Duplicate {kind} archive path: {name!r}')
    seen.add(normalized)
    return normalized

def validate_hierarchy(entries):
    entry_types = {name: entry_type for _, name, entry_type in entries}
    for name, entry_type in entry_types.items():
        parent = posixpath.dirname(name)
        while parent:
            if entry_types.get(parent) == 'file':
                raise SystemExit(f'Conflicting {kind} archive paths: {parent!r} and {name!r}')
            parent = posixpath.dirname(parent)
        if entry_type == 'file' and any(other.startswith(name + '/') for other in entry_types):
            raise SystemExit(f'Conflicting {kind} archive file/directory path: {name!r}')

def sanitized_regular_mode(mode):
    # Match tarfile.data_filter: remove high bits and group/other write,
    # preserve executability only when the owner-execute bit is present, and
    # ensure the owner can always read and write the extracted regular file.
    mode &= 0o755
    if not mode & 0o100:
        mode &= ~0o111
    return mode | 0o600

if kind == 'tar':
    entries = []
    seen = set()
    total_bytes = 0
    with tarfile.open(archive, 'r:*') as source:
        # Iterate lazily and stop at the cap instead of materializing an
        # unbounded member list with getmembers().
        for member in source:
            if len(entries) >= max_members:
                raise SystemExit(f'{kind} archive exceeds {max_members} members')
            name = validate_name(member.name, seen)
            if member.isdir():
                entry_type = 'directory'
            elif member.isreg():
                entry_type = 'file'
            else:
                raise SystemExit(f'Unsupported tar archive member type: {member.name!r}')
            if member.size > max_member_bytes:
                raise SystemExit(f'Tar archive member exceeds {max_member_bytes} bytes: {member.name!r}')
            total_bytes += member.size
            if total_bytes > max_total_bytes:
                raise SystemExit(f'Tar archive exceeds {max_total_bytes} extracted bytes')
            entries.append((member, name, entry_type))
        # crates.io packages may omit an explicit directory member while
        # placing every file below one root. validate_name() still rejects
        # any member outside that required root.
        if expected_root not in seen and not any(
                name.startswith(expected_root + '/') for _, name, _ in entries):
            raise SystemExit(f'{kind} archive is missing its required root: {expected_root}')
        validate_hierarchy(entries)
        for member, name, entry_type in entries:
            target = destination / name
            if entry_type == 'directory':
                # Like tarfile.data_filter, ignore archive directory modes.
                target.mkdir(parents=True, exist_ok=True)
                continue

            target.parent.mkdir(parents=True, exist_ok=True)
            input_file = source.extractfile(member)
            if input_file is None:
                raise SystemExit(f'Could not read regular tar archive member: {member.name!r}')
            with input_file, open(target, 'xb') as output_file:
                shutil.copyfileobj(input_file, output_file, length=1024 * 1024)
            if target.stat().st_size != member.size:
                raise SystemExit(f'Tar archive member size did not match: {member.name!r}')
            os.chmod(target, sanitized_regular_mode(member.mode))
elif kind == 'zip':
    seen = set()
    with zipfile.ZipFile(archive) as source:
        entries = source.infolist()
        validated_entries = []
        if len(entries) > max_members:
            raise SystemExit(f'{kind} archive exceeds {max_members} members')
        total_bytes = 0
        for member in entries:
            name = validate_name(member.filename, seen)
            if member.flag_bits & 0x1:
                raise SystemExit(f'Encrypted zip archive member is unsupported: {member.filename!r}')
            if member.file_size > max_member_bytes:
                raise SystemExit(f'Zip archive member exceeds {max_member_bytes} bytes: {member.filename!r}')
            total_bytes += member.file_size
            if total_bytes > max_total_bytes:
                raise SystemExit(f'Zip archive exceeds {max_total_bytes} extracted bytes')
            mode = (member.external_attr >> 16) & 0o170000
            if member.is_dir():
                if mode not in (0, stat.S_IFDIR):
                    raise SystemExit(f'Unsupported zip directory member type: {member.filename!r}')
                entry_type = 'directory'
            else:
                if mode not in (0, stat.S_IFREG):
                    raise SystemExit(f'Unsupported zip archive member type: {member.filename!r}')
                entry_type = 'file'
            validated_entries.append((member, name, entry_type))
        if expected_root not in seen and not any(
                name.startswith(expected_root + '/') for _, name, _ in validated_entries):
            raise SystemExit(f'{kind} archive is missing its required root: {expected_root}')
        validate_hierarchy(validated_entries)
        for member, name, entry_type in validated_entries:
            target = destination / name
            if entry_type == 'directory':
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.open(member) as input_file, open(target, 'xb') as output_file:
                    shutil.copyfileobj(input_file, output_file, length=1024 * 1024)
                if target.stat().st_size != member.file_size:
                    raise SystemExit(f'Zip archive member size did not match: {member.filename!r}')
                permissions = (member.external_attr >> 16) & 0o777
                if permissions:
                    os.chmod(target, sanitized_regular_mode(permissions))
else:
    raise SystemExit(f'Unsupported archive kind: {kind}')

root = destination / expected_root
if not root.is_dir() or root.is_symlink():
    raise SystemExit(f'{kind} archive did not extract a regular single root: {expected_root}')
PYTHON
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

ensure_cvc5() {
  mkdir -p "$(dirname "$CVC5_ARCHIVE")"
  # Only a checksum-verified archive is reusable. Re-extract it every time so
  # an extracted solver binary from a restored cache is never trusted.
  download "$CVC5_URL" "$CVC5_ARCHIVE" "$CVC5_ZIP_SHA256"
  local extract_dir="$TMP_DIR/cvc5-${CVC5_VERSION}-extract"
  safe_extract_archive "$CVC5_ARCHIVE" zip "$extract_dir" 'cvc5-Linux-x86_64-static'
  rm -rf "$CVC5_DIR"
  mv "$extract_dir/cvc5-Linux-x86_64-static" "$CVC5_DIR"
  rmdir "$extract_dir"
  if [[ ! -x "$CVC5_BIN" || -L "$CVC5_BIN" ]]; then
    echo 'cvc5 archive did not contain a regular Linux x86-64 cvc5 executable' >&2
    return 1
  fi
  local version_output
  version_output="$($CVC5_BIN --version 2>&1)"
  if ! grep -Fq "cvc5 $CVC5_VERSION" <<< "$version_output" \
      || ! grep -Fq "git ${CVC5_COMMIT:0:7}" <<< "$version_output"; then
    echo 'cvc5 binary version/commit did not match the manifest' >&2
    printf '%s\n' "$version_output" >&2
    return 1
  fi
}

ensure_carcara() {
  require_command rustup rustup
  require_command cargo cargo
  require_command python3 python3
  require_command m4 m4
  require_command cc build-essential
  require_command make build-essential
  mkdir -p "$(dirname "$CARCARA_ARCHIVE")" "$CARCARA_RUSTUP_HOME" "$CARCARA_CARGO_HOME"
  # Keep verified source and the dated Rust manifest in cache, but always
  # re-extract and rebuild Carcara from Cargo.lock on every invocation.
  download "$CARCARA_URL" "$CARCARA_ARCHIVE" "$CARCARA_TAR_SHA256"
  download "$CARCARA_RUST_MANIFEST_URL" "$CARCARA_RUST_MANIFEST" "$CARCARA_RUST_MANIFEST_SHA256"
  python3 - "$CARCARA_RUST_MANIFEST" "$CARCARA_RUST_TOOLCHAIN" "$CARCARA_RUSTC_COMMIT" "$CARCARA_CARGO_COMMIT" "$CARCARA_RUST_HOST" <<'PYTHON'
import sys

try:
    import tomllib
except ModuleNotFoundError:
    raise SystemExit(
        'Carcara Rust-manifest verification requires Python 3.11 or later '
        '(the standard-library tomllib module is unavailable)'
    ) from None

manifest_path, release, rustc_commit, cargo_commit, host = sys.argv[1:]
with open(manifest_path, 'rb') as stream:
    manifest = tomllib.load(stream)
if manifest.get('manifest-version') != '2':
    raise SystemExit('Rust channel manifest version is not 2')
rustc = manifest.get('pkg', {}).get('rustc', {})
cargo = manifest.get('pkg', {}).get('cargo', {})
if rustc.get('git_commit_hash') != rustc_commit or not rustc.get('version', '').startswith(f'{release} '):
    raise SystemExit('Rust channel manifest rustc provenance did not match the tool manifest')
if cargo_commit[:9] not in cargo.get('version', ''):
    raise SystemExit('Rust channel manifest Cargo provenance did not match the tool manifest')
for package_name in ('rustc', 'cargo', 'rust-std'):
    target = manifest.get('pkg', {}).get(package_name, {}).get('target', {}).get(host, {})
    if target.get('available') is not True:
        raise SystemExit(f'Rust channel manifest does not provide {package_name} for {host}')
PYTHON
  RUSTUP_HOME="$CARCARA_RUSTUP_HOME" CARGO_HOME="$CARCARA_CARGO_HOME" \
    rustup toolchain install "$CARCARA_RUST_TOOLCHAIN" --profile minimal --no-self-update

  local rustc_version_output cargo_version_output
  rustc_version_output="$(RUSTUP_HOME="$CARCARA_RUSTUP_HOME" CARGO_HOME="$CARCARA_CARGO_HOME" \
    rustc "+$CARCARA_RUST_TOOLCHAIN" --version --verbose)"
  cargo_version_output="$(RUSTUP_HOME="$CARCARA_RUSTUP_HOME" CARGO_HOME="$CARCARA_CARGO_HOME" \
    cargo "+$CARCARA_RUST_TOOLCHAIN" --version --verbose)"
  for expected in \
    "release: $CARCARA_RUST_TOOLCHAIN" \
    "commit-hash: $CARCARA_RUSTC_COMMIT" \
    "host: $CARCARA_RUST_HOST"; do
    if ! grep -Fxq "$expected" <<< "$rustc_version_output"; then
      echo "Installed rustc provenance did not match: $expected" >&2
      return 1
    fi
  done
  for expected in \
    "release: $CARCARA_RUST_TOOLCHAIN" \
    "commit-hash: $CARCARA_CARGO_COMMIT" \
    "host: $CARCARA_RUST_HOST"; do
    if ! grep -Fxq "$expected" <<< "$cargo_version_output"; then
      echo "Installed Cargo provenance did not match: $expected" >&2
      return 1
    fi
  done

  local extract_dir="$TMP_DIR/carcara-${CARCARA_COMMIT}-extract"
  safe_extract_archive "$CARCARA_ARCHIVE" tar "$extract_dir" "carcara-${CARCARA_COMMIT}"
  local source_dir="$extract_dir/carcara-${CARCARA_COMMIT}"
  if [[ "$(sha256_of "$source_dir/Cargo.lock")" != "$CARCARA_CARGO_LOCK_SHA256" ]]; then
    echo 'Carcara Cargo.lock digest did not match the manifest' >&2
    return 1
  fi
  rm -rf "$CARCARA_DIR"
  RUSTUP_HOME="$CARCARA_RUSTUP_HOME" CARGO_HOME="$CARCARA_CARGO_HOME" \
    CARGO_TARGET_DIR="$CARCARA_DIR/target" \
    cargo "+$CARCARA_RUST_TOOLCHAIN" build --quiet --locked --release --package carcara-cli --manifest-path "$source_dir/Cargo.toml"
  rm -rf "$extract_dir"
  if [[ ! -x "$CARCARA_BIN" || -L "$CARCARA_BIN" ]]; then
    echo 'Carcara build did not produce the expected regular executable' >&2
    return 1
  fi
  local version_output
  version_output="$($CARCARA_BIN --version 2>&1)"
  if ! grep -Eq "^carcara ${CARCARA_VERSION//./\\.}( |$)" <<< "$version_output"; then
    echo 'Carcara binary version did not match the manifest' >&2
    printf '%s\n' "$version_output" >&2
    return 1
  fi
}


ensure_rtlola_locked() {
  require_command rustup rustup
  require_command cargo cargo
  require_command python3 python3
  require_command cc build-essential
  mkdir -p "$(dirname "$RTLOLA_ARCHIVE")" "$RTLOLA_RUSTUP_HOME" "$RTLOLA_CARGO_HOME"

  # crates.io packages are immutable. Verify the package and its embedded
  # Cargo.lock/VCS provenance, then rebuild in tools/.tmp on every invocation.
  download "$RTLOLA_URL" "$RTLOLA_ARCHIVE" "$RTLOLA_CRATE_SHA256"
  download "$RTLOLA_RUST_MANIFEST_URL" "$RTLOLA_RUST_MANIFEST" "$RTLOLA_RUST_MANIFEST_SHA256"
  python3 - "$RTLOLA_RUST_MANIFEST" "$RTLOLA_RUST_TOOLCHAIN" "$RTLOLA_RUSTC_COMMIT" "$RTLOLA_CARGO_COMMIT" "$RTLOLA_RUST_HOST" <<'PYTHON'
import sys

try:
    import tomllib
except ModuleNotFoundError:
    raise SystemExit(
        'RTLola Rust-manifest verification requires Python 3.11 or later '
        '(the standard-library tomllib module is unavailable)'
    ) from None

manifest_path, release, rustc_commit, cargo_commit, host = sys.argv[1:]
with open(manifest_path, 'rb') as stream:
    manifest = tomllib.load(stream)
if manifest.get('manifest-version') != '2':
    raise SystemExit('Rust channel manifest version is not 2')
rustc = manifest.get('pkg', {}).get('rustc', {})
cargo = manifest.get('pkg', {}).get('cargo', {})
if rustc.get('git_commit_hash') != rustc_commit or not rustc.get('version', '').startswith(release + ' '):
    raise SystemExit('Rust channel manifest rustc provenance did not match the RTLola tool manifest')
if cargo_commit[:9] not in cargo.get('version', ''):
    raise SystemExit('Rust channel manifest Cargo provenance did not match the RTLola tool manifest')
for package_name in ('rustc', 'cargo', 'rust-std'):
    target = manifest.get('pkg', {}).get(package_name, {}).get('target', {}).get(host, {})
    if target.get('available') is not True:
        raise SystemExit('Rust channel manifest does not provide ' + package_name + ' for ' + host)
PYTHON
  RUSTUP_HOME="$RTLOLA_RUSTUP_HOME" CARGO_HOME="$RTLOLA_CARGO_HOME" \
    rustup toolchain install "$RTLOLA_RUST_TOOLCHAIN" --profile minimal --no-self-update

  local rustc_version_output cargo_version_output
  rustc_version_output="$(RUSTUP_HOME="$RTLOLA_RUSTUP_HOME" CARGO_HOME="$RTLOLA_CARGO_HOME" \
    rustc "+$RTLOLA_RUST_TOOLCHAIN" --version --verbose)"
  cargo_version_output="$(RUSTUP_HOME="$RTLOLA_RUSTUP_HOME" CARGO_HOME="$RTLOLA_CARGO_HOME" \
    cargo "+$RTLOLA_RUST_TOOLCHAIN" --version --verbose)"
  local expected
  for expected in \
    "release: $RTLOLA_RUST_TOOLCHAIN" \
    "commit-hash: $RTLOLA_RUSTC_COMMIT" \
    "host: $RTLOLA_RUST_HOST"; do
    if ! grep -Fxq "$expected" <<< "$rustc_version_output"; then
      echo "Installed RTLola rustc provenance did not match: $expected" >&2
      return 1
    fi
  done
  for expected in \
    "release: $RTLOLA_RUST_TOOLCHAIN" \
    "commit-hash: $RTLOLA_CARGO_COMMIT" \
    "host: $RTLOLA_RUST_HOST"; do
    if ! grep -Fxq "$expected" <<< "$cargo_version_output"; then
      echo "Installed RTLola Cargo provenance did not match: $expected" >&2
      return 1
    fi
  done

  local extract_dir="$TMP_DIR/rtlola-$RTLOLA_VERSION-extract"
  safe_extract_archive "$RTLOLA_ARCHIVE" tar "$extract_dir" "rtlola-cli-$RTLOLA_VERSION"
  local source_dir="$extract_dir/rtlola-cli-$RTLOLA_VERSION"
  if [[ "$(sha256_of "$source_dir/Cargo.lock")" != "$RTLOLA_CARGO_LOCK_SHA256" ]]; then
    echo 'RTLola Cargo.lock digest did not match the manifest' >&2
    return 1
  fi
  python3 - "$source_dir/.cargo_vcs_info.json" "$RTLOLA_COMMIT" <<'PYTHON'
import json
import sys

with open(sys.argv[1], encoding='utf-8') as stream:
    value = json.load(stream)
if value != {'git': {'sha1': sys.argv[2]}, 'path_in_vcs': 'crates/rtlola-cli'}:
    raise SystemExit('RTLola package VCS provenance did not match the manifest')
PYTHON

  rm -rf "$RTLOLA_DIR"
  mkdir -p "$RTLOLA_DIR"
  RUSTUP_HOME="$RTLOLA_RUSTUP_HOME" CARGO_HOME="$RTLOLA_CARGO_HOME" \
    CARGO_TARGET_DIR="$RTLOLA_DIR/target" \
    cargo "+$RTLOLA_RUST_TOOLCHAIN" build --quiet --locked --release \
      --manifest-path "$source_dir/Cargo.toml"
  rm -rf "$extract_dir"
  if [[ ! -x "$RTLOLA_BIN" || -L "$RTLOLA_BIN" ]]; then
    echo 'RTLola build did not produce the expected regular executable' >&2
    return 1
  fi
  if [[ "$("$RTLOLA_BIN" --version)" != "rtlola-cli $RTLOLA_VERSION" ]]; then
    echo 'RTLola binary version did not match the manifest' >&2
    return 1
  fi
}

ensure_rtlola() {
  require_command flock util-linux
  local lock_file="$TMP_DIR/rtlola-$RTLOLA_VERSION.lock"
  mkdir -p "$(dirname "$lock_file")"

  # Both teaching contracts rebuild into the same verified target path. A
  # worktree may launch them concurrently outside the official sequential
  # matrix runner, so serialize extraction and build rather than allowing one
  # process to remove another process's source or target directory.
  (
    if ! flock -x -w 300 9; then
      echo 'Timed out waiting for the RTLola bootstrap lock' >&2
      return 75
    fi
    ensure_rtlola_locked
  ) 9>"$lock_file"
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

ensure_sby() {
  require_command python3 python3
  require_command timeout coreutils
  mkdir -p "$(dirname "$SBY_ARCHIVE")"
  # The archive is the only reusable SBY cache object.  Never trust an
  # extracted tree: validate and regenerate it on every bootstrap invocation.
  download "$SBY_URL" "$SBY_ARCHIVE" "$SBY_TAR_SHA256"
  rm -rf "$SBY_SUITE_DIR"
  mkdir -p "$SBY_SUITE_DIR"

  python3 - "$SBY_ARCHIVE" "$SBY_SUITE_DIR" <<'PYTHON'
import os
import posixpath
import sys
import tarfile
from pathlib import Path

archive, destination = map(Path, sys.argv[1:])
root = 'oss-cad-suite'
seen = set()
entries = []

def unsafe(name):
    return (not name or name.startswith('/') or '\\' in name or
            posixpath.normpath(name) != name or name == '..' or name.startswith('../'))

def link_target_is_safe(member):
    target = member.linkname
    if not target or target.startswith('/') or '\\' in target:
        return False
    candidate = posixpath.normpath(posixpath.join(posixpath.dirname(member.name), target))
    return candidate == root or candidate.startswith(root + '/')

with tarfile.open(archive, 'r:gz') as tar:
    for member in tar.getmembers():
        name = member.name.rstrip('/')
        if unsafe(name) or not (name == root or name.startswith(root + '/')):
            raise SystemExit(f'Unsafe OSS CAD Suite archive path: {member.name!r}')
        if name in seen:
            raise SystemExit(f'Duplicate OSS CAD Suite archive path: {member.name!r}')
        seen.add(name)
        if member.isdir() or member.isreg():
            pass
        elif member.issym():
            if not link_target_is_safe(member):
                raise SystemExit(f'Unsafe OSS CAD Suite archive link: {member.name!r} -> {member.linkname!r}')
        else:
            raise SystemExit(f'Unsupported OSS CAD Suite archive member type: {member.name!r}')
        entries.append(member)
    if not any(member.name.rstrip('/') == root for member in entries):
        raise SystemExit('OSS CAD Suite archive must contain exactly the oss-cad-suite root')
    # Every member was path- and link-validated above before extraction.
    tar.extractall(destination, members=entries, filter='data')

suite = destination / root
if not suite.is_dir() or suite.is_symlink():
    raise SystemExit('OSS CAD Suite extraction did not produce a regular oss-cad-suite root')
PYTHON
  local suite_root="$SBY_SUITE_DIR/oss-cad-suite"
  local version_file="$suite_root/VERSION"
  local sby_bin="$suite_root/bin/sby"
  local yosys_bin="$suite_root/bin/yosys"
  local bitwuzla_bin="$suite_root/bin/bitwuzla"
  if [[ ! -f "$version_file" || -L "$version_file" || ! -x "$sby_bin" || ! -x "$yosys_bin" || ! -x "$bitwuzla_bin" ]]; then
    echo 'OSS CAD Suite archive did not contain the expected VERSION and executable layout' >&2
    return 1
  fi
  if ! grep -Fxq "$SBY_SUITE_VERSION" "$version_file"; then
    echo "OSS CAD Suite VERSION did not match manifest: $SBY_SUITE_VERSION" >&2
    return 1
  fi
  local sby_output yosys_output bitwuzla_output
  sby_output="$($sby_bin --version 2>&1)"
  yosys_output="$($yosys_bin -V 2>&1)"
  bitwuzla_output="$($bitwuzla_bin --version 2>&1)"
  if ! grep -Fq "SBY $SBY_VERSION" <<< "$sby_output"; then
    echo 'SymbiYosys version/commit did not match the manifest' >&2
    printf '%s\n' "$sby_output" >&2
    return 1
  fi
  if ! grep -Fq "Yosys $SBY_YOSYS_VERSION" <<< "$yosys_output"; then
    echo 'Yosys version/commit did not match the manifest' >&2
    printf '%s\n' "$yosys_output" >&2
    return 1
  fi
  if [[ "$bitwuzla_output" != "$SBY_BITWUZLA_VERSION" ]]; then
    echo 'Bitwuzla version/commit did not match the manifest' >&2
    printf '%s\n' "$bitwuzla_output" >&2
    return 1
  fi
  # The suite records source provenance in bundled license headers. Require a
  # component-labelled header for each pinned source commit, rather than
  # accepting an unrelated occurrence elsewhere in the extracted tree.
  local component commit component_pattern header
  for component in sby yosys bitwuzla; do
    case "$component" in
      sby) commit="$SBY_COMMIT"; component_pattern='sby|symbiyosys' ;;
      yosys) commit="$SBY_YOSYS_COMMIT"; component_pattern='yosys' ;;
      bitwuzla) commit="$SBY_BITWUZLA_COMMIT"; component_pattern='bitwuzla' ;;
    esac
    header="$(while IFS= read -r -d '' candidate; do
      if grep -Eiq "$component_pattern" "$candidate" && grep -Fq "$commit" "$candidate"; then
        printf '%s\n' "$candidate"
        break
      fi
    done < <(find "$suite_root" -type f \( -iname '*license*' -o -iname '*copying*' -o -iname '*notice*' \) -print0))"
    if [[ -z "$header" ]]; then
      echo "Bundled license header did not bind $component to source commit $commit" >&2
      return 1
    fi
  done
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

if [[ "${FORMAL_BOOTSTRAP_LIBRARY_ONLY:-0}" == "1" ]]; then
  return 0 2>/dev/null || exit 0
fi

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
    cvc5) ensure_cvc5; ensure_carcara; installed+=("cvc5 ${CVC5_VERSION} + Carcara ${CARCARA_VERSION}") ;;
    rtlola) ensure_rtlola; installed+=("RTLola CLI $RTLOLA_VERSION ($RTLOLA_COMMIT)") ;;
    tamarin) ensure_tamarin; installed+=("Tamarin ${TAMARIN_VERSION} (Maude ${TAMARIN_MAUDE_VERSION})") ;;
    sby) ensure_sby; installed+=("SymbiYosys ${SBY_VERSION} (OSS CAD Suite ${SBY_SUITE_VERSION})") ;;
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

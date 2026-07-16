#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TEST_ROOT="$REPO_ROOT/.artifacts/tests/safe-extract-archive"
trap 'rm -rf "$TEST_ROOT"' EXIT
rm -rf "$TEST_ROOT"
mkdir -p "$TEST_ROOT"
umask 022

# Load the production extraction function without installing any tool.
FORMAL_BOOTSTRAP_LIBRARY_ONLY=1 source "$REPO_ROOT/tools/bootstrap.sh" --tool cvc5

python3 - "$TEST_ROOT" <<'PYTHON'
import io
import stat
import sys
import tarfile
import zipfile
from pathlib import Path

root = Path(sys.argv[1])

def tar_entry(archive, name, mode=0o644, data=b'', entry_type=tarfile.REGTYPE, linkname=''):
    member = tarfile.TarInfo(name)
    member.mode = mode
    member.type = entry_type
    member.linkname = linkname
    member.size = len(data) if entry_type == tarfile.REGTYPE else 0
    archive.addfile(member, io.BytesIO(data) if member.size else None)

with tarfile.open(root / 'permissions.tar', 'w') as archive:
    tar_entry(archive, 'root', 0o777, entry_type=tarfile.DIRTYPE)
    tar_entry(archive, 'root/nested', 0o000, entry_type=tarfile.DIRTYPE)
    for label, mode in (('zero', 0o000), ('read', 0o400), ('write', 0o666), ('exec', 0o777)):
        tar_entry(archive, f'root/nested/{label}', mode, label.encode())

for label, name, entry_type, linkname in (
    ('symlink', 'root/link', tarfile.SYMTYPE, 'target'),
    ('hardlink', 'root/link', tarfile.LNKTYPE, 'root/target'),
    ('fifo', 'root/fifo', tarfile.FIFOTYPE, ''),
    ('traversal', 'root/../escape', tarfile.REGTYPE, ''),
    ('absolute', '/root/file', tarfile.REGTYPE, ''),
    ('backslash', 'root\\file', tarfile.REGTYPE, ''),
):
    with tarfile.open(root / f'reject-{label}.tar', 'w') as archive:
        tar_entry(archive, 'root', entry_type=tarfile.DIRTYPE)
        tar_entry(archive, name, entry_type=entry_type, linkname=linkname)

for label, names in (
    ('duplicate', ('root/file', 'root/file')),
    ('parent-file', ('root/file', 'root/file/child')),
    ('child-before-file', ('root/file/child', 'root/file')),
):
    with tarfile.open(root / f'conflict-{label}.tar', 'w') as archive:
        tar_entry(archive, 'root', entry_type=tarfile.DIRTYPE)
        for name in names:
            tar_entry(archive, name, data=b'x')

with tarfile.open(root / 'member-cap.tar', 'w') as archive:
    tar_entry(archive, 'root', entry_type=tarfile.DIRTYPE)
    for index in range(4096):
        tar_entry(archive, f'root/{index:04d}')

with zipfile.ZipFile(root / 'valid.zip', 'w') as archive:
    directory = zipfile.ZipInfo('root/')
    directory.external_attr = (stat.S_IFDIR | 0o777) << 16
    archive.writestr(directory, b'')
    regular = zipfile.ZipInfo('root/tool')
    regular.external_attr = (stat.S_IFREG | 0o777) << 16
    archive.writestr(regular, b'tool')

with zipfile.ZipFile(root / 'reject-symlink.zip', 'w') as archive:
    directory = zipfile.ZipInfo('root/')
    directory.external_attr = (stat.S_IFDIR | 0o755) << 16
    archive.writestr(directory, b'')
    link = zipfile.ZipInfo('root/link')
    link.external_attr = (stat.S_IFLNK | 0o777) << 16
    archive.writestr(link, b'target')
PYTHON

safe_extract_archive "$TEST_ROOT/permissions.tar" tar "$TEST_ROOT/permissions-out" root
declare -A expected_modes=(
  [zero]=600
  [read]=600
  [write]=644
  [exec]=755
)
for file in "${!expected_modes[@]}"; do
  actual="$(stat -c '%a' "$TEST_ROOT/permissions-out/root/nested/$file")"
  if [[ "$actual" != "${expected_modes[$file]}" ]]; then
    echo "Unexpected sanitized mode for $file: $actual" >&2
    exit 1
  fi
done
for directory in root root/nested; do
  actual="$(stat -c '%a' "$TEST_ROOT/permissions-out/$directory")"
  if [[ "$actual" != "755" ]]; then
    echo "Archive directory mode was not ignored for $directory: $actual" >&2
    exit 1
  fi
done

for archive in "$TEST_ROOT"/reject-*.tar "$TEST_ROOT"/conflict-*.tar; do
  label="$(basename "$archive" .tar)"
  if safe_extract_archive "$archive" tar "$TEST_ROOT/$label-out" root >/dev/null 2>&1; then
    echo "Unsafe tar archive was accepted: $label" >&2
    exit 1
  fi
done

if member_cap_output="$(safe_extract_archive "$TEST_ROOT/member-cap.tar" tar "$TEST_ROOT/member-cap-out" root 2>&1)"; then
  echo 'Tar member cap was not enforced' >&2
  exit 1
fi
grep -Fq 'exceeds 4096 members' <<< "$member_cap_output"

safe_extract_archive "$TEST_ROOT/valid.zip" zip "$TEST_ROOT/zip-out" root
test "$(stat -c '%a' "$TEST_ROOT/zip-out/root/tool")" = '755'
if safe_extract_archive "$TEST_ROOT/reject-symlink.zip" zip "$TEST_ROOT/zip-symlink-out" root >/dev/null 2>&1; then
  echo 'Zip symlink was accepted' >&2
  exit 1
fi

echo 'Safe archive extraction tests passed (permissions, paths, types, collisions, caps, zip).'

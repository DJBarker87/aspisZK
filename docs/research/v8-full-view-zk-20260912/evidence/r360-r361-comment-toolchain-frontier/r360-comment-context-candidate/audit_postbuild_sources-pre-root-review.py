#!/usr/bin/env python3
"""Read-only postbuild inventory for R360; writes audit artifacts only after all checks pass."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, stat, time

ROOT = Path('/home/dombarker/project-offloads/aspis-r360-comment-context-candidate-20261002-a')
SRC = ROOT / 'src'
AUDIT = ROOT / 'candidate-audit'
PARENT = Path('/home/dombarker/project-offloads/aspis-r349-output-name-alpha-candidate-20261002-a')
PARENT_SRC = PARENT / 'src'
R360_PREBUILD = AUDIT / 'candidate-tree-manifest.json'
R349_SAVED = ROOT / 'R349-candidate-tree-manifest.json'
R360_BINARY = ROOT / 'aeneas-r360-comment-context-candidate'
EXPECTED = {
    'R360_extract': '0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527',
    'R349_extract': 'cb59112741c428671764a44af7478117d2a324270ac0aec5c41052a3a2833a25',
    'TranslateCore': '4f5db3cd77a10a3861539958d7b8566f09e6bcc3b72981fcc40388611d639cb9',
    'InterpExpansion': 'da68f59bc0240bad9862f0733aecd7265c239dbe988669d5d8ddddafc5a79b19',
    'PrePasses': '09014aa93bffd2cafeebaf23d27a301d66986d9349f4cc9dca6e8d1dfe0ba7dd',
    'R360_prebuild_manifest': '27820ee9cc6706001009c240280c24d156c0dff9e52e8b130dccb815ca7d05e2',
    'R349_saved_manifest': 'b18fe0f5e8451a0cd699ebf27016a543b3421792ee71154d9c3a4cf81b9ace62',
    'R349_binary': 'dc4b9d209c645a0d951bdd78f7e0f9d6fb9d09b0e88491edded1ee7beb791cd6',
}


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def inventory(root):
    rows = []
    for path in sorted(root.rglob('*')):
        rel = path.relative_to(root).as_posix()
        st = path.lstat()
        if stat.S_ISLNK(st.st_mode):
            rows.append({'path': rel, 'kind': 'symlink', 'target': os.readlink(path), 'mode': stat.S_IMODE(st.st_mode), 'mtime_ns': st.st_mtime_ns})
        elif stat.S_ISDIR(st.st_mode):
            rows.append({'path': rel, 'kind': 'directory', 'mode': stat.S_IMODE(st.st_mode), 'mtime_ns': st.st_mtime_ns})
        elif stat.S_ISREG(st.st_mode):
            rows.append({'path': rel, 'kind': 'file', 'size': st.st_size, 'sha256': sha_file(path), 'mode': stat.S_IMODE(st.st_mode), 'mtime_ns': st.st_mtime_ns})
        else:
            raise RuntimeError(f'unsupported filesystem entry: {path}')
    return rows


def compare_row(row):
    return {k: v for k, v in row.items() if k != 'mtime_ns'}


def by_path(rows):
    result = {row['path']: row for row in rows}
    if len(result) != len(rows):
        raise RuntimeError('duplicate path in manifest')
    return result


def non_build_differences(actual, expected):
    a, e = by_path(actual), by_path(expected)
    paths = sorted((a.keys() | e.keys()) - {p for p in a.keys() | e.keys() if p == '_build' or p.startswith('_build/')})
    return [p for p in paths if p not in a or p not in e or compare_row(a[p]) != compare_row(e[p])]


def regular_inode_set(root):
    out = set()
    for path in root.rglob('*'):
        if path.is_symlink():
            continue
        try:
            st = path.stat(follow_symlinks=False)
        except FileNotFoundError as error:
            raise RuntimeError(f'filesystem changed while collecting inode inventory: {path}') from error
        if stat.S_ISREG(st.st_mode):
            out.add((st.st_dev, st.st_ino))
    return out


started = datetime.now(timezone.utc).isoformat(timespec='microseconds')
assert SRC.is_dir() and PARENT_SRC.is_dir()
assert AUDIT.is_dir() and not AUDIT.is_symlink()
assert R360_PREBUILD.is_file() and R349_SAVED.is_file()
assert R360_BINARY.is_file(), f'expected postbuild executable missing: {R360_BINARY}'

prebuild_bytes = R360_PREBUILD.read_bytes()
r349_saved_bytes = R349_SAVED.read_bytes()
assert sha_bytes(prebuild_bytes) == EXPECTED['R360_prebuild_manifest']
assert sha_bytes(r349_saved_bytes) == EXPECTED['R349_saved_manifest']
prebuild = json.loads(prebuild_bytes)
r349_saved = json.loads(r349_saved_bytes)

candidate_current = inventory(SRC)
parent_current = inventory(PARENT_SRC)
# R360 postbuild source tree must differ from its saved prebuild snapshot only under _build.
changed = sorted(
    path for path in by_path(candidate_current).keys() | by_path(prebuild).keys()
    if path not in by_path(candidate_current)
    or path not in by_path(prebuild)
    or compare_row(by_path(candidate_current)[path]) != compare_row(by_path(prebuild)[path])
)
non_build_changed = [path for path in changed if not (path == '_build' or path.startswith('_build/'))]
assert not non_build_changed, f'R360 non-build path changed since saved prebuild inventory: {non_build_changed}'

# Parent R349's live non-build rows must still match the exact saved R349 manifest.
parent_non_build_changed = non_build_differences(parent_current, r349_saved)
assert not parent_non_build_changed, f'R349 parent non-build rows differ from saved manifest: {parent_non_build_changed}'

# The R360 clone is expected to differ from R349 only at its already-approved ExtractTypes source file.
clone_non_build_changed = non_build_differences(candidate_current, parent_current)
assert clone_non_build_changed == ['extract/ExtractTypes.ml'], clone_non_build_changed
assert sha_file(SRC / 'extract/ExtractTypes.ml') == EXPECTED['R360_extract']
assert sha_file(PARENT_SRC / 'extract/ExtractTypes.ml') == EXPECTED['R349_extract']
for rel in ('TranslateCore.ml', 'interp/InterpExpansion.ml', 'PrePasses.ml'):
    assert sha_file(SRC / rel) == EXPECTED[rel.split('/')[-1] if rel != 'interp/InterpExpansion.ml' else 'InterpExpansion']
    assert sha_file(PARENT_SRC / rel) == EXPECTED[rel.split('/')[-1] if rel != 'interp/InterpExpansion.ml' else 'InterpExpansion']

parent_inodes = regular_inode_set(PARENT_SRC)
candidate_inodes = regular_inode_set(SRC)
shared_inodes = parent_inodes & candidate_inodes
assert not shared_inodes, f'shared regular-file inodes detected: {len(shared_inodes)}'

binary_sha = sha_file(R360_BINARY)
binary_size = R360_BINARY.stat().st_size
assert binary_size > 0
finished = datetime.now(timezone.utc).isoformat(timespec='microseconds')

# Output directory is unique and guarded. All source-tree reads/checks above finish before any write.
out = AUDIT / 'postbuild-source-audit'
assert not out.exists(), f'refusing to overwrite existing postbuild audit: {out}'
out.mkdir(mode=0o755)
(out / 'candidate-current-manifest.json').write_text(json.dumps(candidate_current, indent=2) + '\n')
(out / 'parent-r349-current-manifest.json').write_text(json.dumps(parent_current, indent=2) + '\n')
(out / 'candidate-prebuild-manifest.json').write_bytes(prebuild_bytes)
(out / 'parent-r349-saved-manifest.json').write_bytes(r349_saved_bytes)
report = {
    'status': 'postbuild source/cache inventory passed; this is not a translation or source-semantics result',
    'started_at_utc': started,
    'finished_at_utc': finished,
    'captured_at_unix_ns': time.time_ns(),
    'candidate_root': str(ROOT),
    'parent_R349_root': str(PARENT),
    'R360_prebuild_manifest_sha256': sha_bytes(prebuild_bytes),
    'R349_saved_manifest_sha256': sha_bytes(r349_saved_bytes),
    'candidate_current_manifest_sha256': sha_bytes((out / 'candidate-current-manifest.json').read_bytes()),
    'parent_current_manifest_sha256': sha_bytes((out / 'parent-r349-current-manifest.json').read_bytes()),
    'candidate_current_canonical_tree_sha256': sha_bytes(json.dumps(candidate_current, sort_keys=True, separators=(',', ':')).encode()),
    'parent_current_canonical_tree_sha256': sha_bytes(json.dumps(parent_current, sort_keys=True, separators=(',', ':')).encode()),
    'postbuild_changed_paths_vs_candidate_prebuild': changed,
    'postbuild_changed_path_count_vs_candidate_prebuild': len(changed),
    'all_postbuild_changes_under_build': not non_build_changed,
    'non_build_changed_paths_vs_candidate_prebuild': non_build_changed,
    'parent_non_build_differences_vs_exact_saved_R349_manifest': parent_non_build_changed,
    'candidate_vs_parent_non_build_differences': clone_non_build_changed,
    'candidate_vs_parent_expected_non_build_difference': 'extract/ExtractTypes.ml only',
    'R360_ExtractTypes_sha256': sha_file(SRC / 'extract/ExtractTypes.ml'),
    'R349_ExtractTypes_sha256': sha_file(PARENT_SRC / 'extract/ExtractTypes.ml'),
    'shared_regular_file_inode_count': len(shared_inodes),
    'R360_executable': {'path': str(R360_BINARY), 'sha256': binary_sha, 'size_bytes': binary_size},
    'expected_unchanged_source_hashes': {rel: sha_file(SRC / rel) for rel in ('TranslateCore.ml', 'interp/InterpExpansion.ml', 'PrePasses.ml')},
    'scope': 'No source or toolchain file changed by this helper. It records tree state and executable identity only; no build/translation/proof semantics are inferred.'
}
(out / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
checksums = []
for path in sorted(out.iterdir()):
    if path.is_file() and path.name != 'SHA256SUMS':
        checksums.append(f'{sha_file(path)}  {path.name}')
(out / 'SHA256SUMS').write_text('\n'.join(checksums) + '\n')
# The checksum list also records its own byte identity separately for the launch log.
print(json.dumps({'audit_dir': str(out), 'report': report, 'sha256sums_sha256': sha_file(out / 'SHA256SUMS')}, indent=2))

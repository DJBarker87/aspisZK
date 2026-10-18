#!/usr/bin/env python3
"""Read-only Git/packaging audit. Writes only the requested JSON; no builds."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import tarfile
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[4]
PACKAGE = Path(__file__).resolve().parents[1]
BASE = '1a39ad6081ba1fdaa77f3ce82c94e0619486344a'
ACCEPTED = '6dd9028e9e0d85e1f8fd78405e78c4af6dded3af'
OLD_BIG = 'de8869cff836ba49cda1b66c473b885f11d410e2'
LIMIT = 90_000_000
PREFIX = 'docs/research/100bit-spend-path-20261013/'
EXCEPTIONS = {PREFIX + path for path in (
    'evidence/selected-read-current-20261018/README.md',
    'evidence/selected-read-current-20261018/selected-read-current-accepted.tar.gz',
    'tools/selected-read-current-kit/verify.py',
)}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def resolve(ref):
    return git('rev-parse', ref + '^{commit}').decode().strip()


def tree(ref):
    result = {}
    for entry in git('ls-tree', '-r', '-l', '-z', ref).split(b'\0'):
        if not entry:
            continue
        metadata, path = entry.split(b'\t', 1)
        mode, kind, oid, size = metadata.split()
        result[path.decode()] = {'mode': mode.decode(), 'type': kind.decode(),
                                'blob': oid.decode(), 'bytes': int(size) if size != b'-' else None}
    return result


def ids(ref):
    return {line.split(b' ', 1)[0].decode()
            for line in git('rev-list', '--objects', ref).splitlines()}


def digest_ids(values):
    return hashlib.sha256(('\n'.join(sorted(values)) + '\n').encode()).hexdigest()


def content_hashes(oids):
    """Hash object bytes in bounded chunks; never materialize large blobs."""
    result = {}
    proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for oid in sorted(set(oids)):
            proc.stdin.write((oid + '\n').encode()); proc.stdin.flush()
            got, kind, size = proc.stdout.readline().decode().split()
            assert got == oid and kind == 'blob'
            remaining = int(size); sha = hashlib.sha256()
            while remaining:
                block = proc.stdout.read(min(1_048_576, remaining))
                assert block
                sha.update(block); remaining -= len(block)
            assert proc.stdout.read(1) == b'\n'
            result[oid] = sha.hexdigest()
        proc.stdin.close()
        assert proc.wait() == 0
    finally:
        if proc.poll() is None:
            proc.terminate(); proc.wait()
    return result


def packaging(accepted_tree, head_tree):
    evidence = PACKAGE / 'evidence/selected-read-current-20261018'
    packet_path = evidence / 'packet-manifest.json'
    packet = json.loads(packet_path.read_text())
    assert packet['archive_bytes'] == 107_282_295
    assert packet['archive_sha256'] == '845b29aff9117e9f4cb7ca515343968802c24bcb5c74e6a9fa8bf72ee63fa048'
    original = PREFIX + 'evidence/selected-read-current-20261018/' + packet['archive']
    assert accepted_tree[original]['blob'] == OLD_BIG and original not in head_tree
    assert not (evidence / packet['archive']).exists()
    packet_relative = packet_path.relative_to(ROOT).as_posix()
    assert accepted_tree[packet_relative] == head_tree[packet_relative]
    reassembly = json.loads((evidence / 'reassembly-manifest.json').read_text())
    reconstructed_git_blob = hashlib.sha1(f"blob {packet['archive_bytes']}\0".encode())
    for pin in reassembly['parts']:
        with (evidence / pin['file']).open('rb') as part:
            while block := part.read(1_048_576):
                reconstructed_git_blob.update(block)
    assert reconstructed_git_blob.hexdigest() == OLD_BIG
    spec = importlib.util.spec_from_file_location('archive_parts', PACKAGE / 'tools/selected-read-current-kit/archive_parts.py')
    helper = importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
    with helper.accepted_archive(evidence, packet) as (archive, members):
        names = []; actual_hashes = {}; internal_sums = None
        with tarfile.open(fileobj=archive, mode='r|gz') as tar:
            for member, pin in zip(tar, members, strict=True):
                assert member.isfile() and member.name == pin['name']
                assert member.size == pin['bytes'] and member.type.decode('ascii') == pin['type']
                with tar.extractfile(member) as source:
                    if member.name == 'SHA256SUMS.json':
                        raw = source.read(); internal_sums = json.loads(raw)
                        actual = hashlib.sha256(raw).hexdigest()
                    else:
                        actual = hashlib.file_digest(source, 'sha256').hexdigest()
                assert actual == pin['sha256']
                names.append(member.name); actual_hashes[member.name] = actual
        assert len(names) == len(set(names)) == packet['members'] == 2309
        assert internal_sums == {n: h for n, h in actual_hashes.items() if n != 'SHA256SUMS.json'}
    return {'original_archive_bytes': packet['archive_bytes'],
            'original_archive_sha256': packet['archive_sha256'],
            'reassembled_git_blob': reconstructed_git_blob.hexdigest(),
            'original_absent_from_head_and_worktree': True,
            'packet_manifest_byte_identical': True,
            'packet_manifest_sha256': hashlib.sha256(packet_path.read_bytes()).hexdigest(),
            'parts': reassembly['parts'], 'member_count': len(names),
            'ordered_member_and_internal_hash_manifest': 'PASS',
            'temporary_reassembly': 'automatically removed, outside repository',
            'proof_replay': 'NONE; content/hash audit only'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--head', default='HEAD')
    ap.add_argument('--output', type=Path, default=PACKAGE / 'evidence/checkpoint-recut-20261018/history-audit.json')
    args = ap.parse_args(); head = resolve(args.head); base = resolve(BASE); accepted = resolve(ACCEPTED)
    commits = git('rev-list', '--reverse', base + '..' + head).decode().splitlines()
    assert commits
    scans = []; all_blobs = set()
    for commit in commits:
        entries = tree(commit); blobs = {p: v for p, v in entries.items() if v['type'] == 'blob'}
        largest_path = max(blobs, key=lambda p: blobs[p]['bytes'])
        oversized = {p: v for p, v in blobs.items() if v['bytes'] > LIMIT}
        scans.append({'commit': commit, 'blob_paths': len(blobs),
                      'unique_blobs': len({v['blob'] for v in blobs.values()}),
                      'maximum_blob': {'path': largest_path, **blobs[largest_path]}, 'oversized': oversized})
        assert not oversized, (commit, oversized)
        all_blobs.update(v['blob'] for v in blobs.values())
    new_objects = ids(base + '..' + head); reachable_objects = ids(head)
    assert OLD_BIG not in new_objects and OLD_BIG not in reachable_objects
    ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', accepted, head], cwd=ROOT).returncode
    assert ancestor == 1
    common = git('merge-base', base, accepted).decode().strip()
    changed = git('diff', '--name-only', '-z', common, accepted).decode().split('\0')[:-1]
    assert len(changed) == 140
    old_tree = tree(accepted); new_tree = tree(head)
    different = {path for path in changed if old_tree.get(path) != new_tree.get(path)}
    assert different == EXCEPTIONS, sorted(different)
    identical = [path for path in changed if path not in different]
    hashes = content_hashes(old_tree[path]['blob'] for path in identical)
    comparisons = [{'path': path, 'accepted': old_tree.get(path), 'head': new_tree.get(path),
                    'byte_identical': path in identical,
                    'sha256': hashes[old_tree[path]['blob']] if path in identical else None}
                   for path in changed]
    package = packaging(old_tree, new_tree)
    report = {'status': 'PASS', 'captured_utc': datetime.now(timezone.utc).isoformat(),
              'base': base, 'accepted_checkpoint': accepted, 'audited_head': head,
              'threshold_bytes': LIMIT, 'new_commits_checked': len(scans), 'commit_tree_scans': scans,
              'all_new_tree_unique_blob_count': len(all_blobs),
              'range_object_count': len(new_objects), 'range_object_id_inventory_sha256': digest_ids(new_objects),
              'head_reachable_object_count': len(reachable_objects),
              'head_reachable_object_id_inventory_sha256': digest_ids(reachable_objects),
              'old_big_blob': OLD_BIG, 'old_big_blob_absent_from_range_and_full_head_ancestry': True,
              'accepted_checkpoint_is_ancestor': False,
              'accepted_content': {'common_ancestor': common, 'changed_paths': len(changed),
                                   'byte_identical': len(identical),
                                   'packaging_only_differences': sorted(different), 'paths': comparisons},
              'packaging': package,
              'scope': 'Read-only Git/object and packaging audit. No Git refs, commits, proof sources, host jobs, compiler or Lean changed.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(f'PASS {len(scans)} commit trees; max {max(s["maximum_blob"]["bytes"] for s in scans)}bytes; old blob/checkpoint absent; 137/140 accepted paths identical, three packaging changes; exact reassembly2309members')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Verify the account-read audit packet without running any build or test."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
packet = Path(__file__).resolve().parent
root = next(p for p in packet.parents if (p / '.git').exists())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
inputs = read(packet / 'input-hashes.json')
assert all(sha(root / p) == h for p, h in inputs.items()), 'Input drift'
frozen = read(packet.parent / 'freeze-20261020/source-hashes.json')
changed = [p for p, h in frozen['files'].items() if sha(root / p) != h]
assert changed == ['programs/r1-cost-probe/src/r1_checkpoint_tests.rs'], changed
remote = read(packet / 'source-validation.json')
assert remote['status'] == 'pass' and remote['mismatches'] == []
assert remote['checked_files'] == len(inputs) == 228
assert remote['input_manifest_sha256'] == sha(packet / 'input-hashes.json')
rec = read(packet / 'receipts/read-teeth/receipt.json')
assert rec['exit_status'] == 0 and rec['swaps'] == 0
assert rec['source_revision'] == (packet / 'source-revision.txt').read_text().strip()
assert rec['limits'] == dict(zip(
    ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max'],
    ['6442450944', '8589934592', '0', '64']))
stdout = (packet / 'receipts/read-teeth/stdout.log').read_text()
assert '2 passed; 0 failed; 0 ignored' in stdout
for name in ['r15_read_binding_rejects_account_buffer_changes_after_stage1',
             'r15_read_stage1_rejects_wrong_lengths_and_non_distinct_accounts']:
    assert f'::{name} ... ok' in stdout
for ref in read(packet / 'parked-writer-references.json'):
    blob = subprocess.check_output(['git', 'show', f"{ref['revision']}:{ref['path']}"], cwd=root)
    assert hashlib.sha256(blob).hexdigest() == ref['sha256']
    assert len(blob) == ref['bytes']
reservation = read(packet / 'reservation.json')
assert reservation['all_populated_scopes_bounded']
assert reservation['bounded_reserved_bytes'] + 8 * 2**30 <= reservation['safe_limit_bytes']
post = read(packet / 'reservation-all-scopes-post.json')
assert post['populated_scopes'] == []
design = root / 'docs/research/100bit-spend-path-20261013/design'
assets = {str(p.relative_to(packet)): {'sha256': sha(p), 'bytes': p.stat().st_size}
          for p in sorted(packet.rglob('*')) if p.is_file() and p.name != 'manifest.json'}
manifest = dict(schema='r15-account-read-audit-v1', source_revision=rec['source_revision'],
    source_delta='Two tests appended to r1_checkpoint_tests.rs; production frozen',
    freeze_revision=frozen['source_revision'],
    unchanged_freeze_inventory_entries=len(frozen['files']) - len(changed),
    changed_freeze_inventory_entries=changed,
    read_audit_sha256=sha(design / 'R15-ADAPTER-READ-AUDIT-20261020.md'),
    write_audit_sha256=sha(design / 'R15-ADAPTER-WRITE-AUDIT-20261020.md'),
    input_files_checked=len(inputs), tests_passed=2, exit_status=rec['exit_status'],
    wall_seconds=rec['wall_seconds'], peak_rss_kib=rec['peak_rss_kib'], swaps=rec['swaps'],
    cgroup_memory_peak_bytes=rec['cgroup_memory_peak_bytes'],
    print_axioms='N/A: no Lean work',
    reservation_limit='Preflight run-* scopes only; corrected all-scope snapshot is post-run',
    assets=assets)
if args.check:
    assert read(packet / 'manifest.json') == manifest, 'Packet/manifest drift'
else:
    (packet / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({k: manifest[k] for k in ['unchanged_freeze_inventory_entries',
    'input_files_checked', 'tests_passed', 'exit_status', 'read_audit_sha256']}))

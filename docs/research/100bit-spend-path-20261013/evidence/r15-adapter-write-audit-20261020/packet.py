#!/usr/bin/env python3
"""Validate this source-audit packet without rebuilding or running tests."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
packet = Path(__file__).resolve().parent
root = next(p for p in packet.parents if (p / '.git').exists())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
inputs = read(packet / 'input-hashes.json')
assert all(sha(root / p) == h for p, h in inputs.items()), 'Source/input drift'
frozen = read(packet.parent / 'freeze-20261020/source-hashes.json')
changed = [p for p, h in frozen['files'].items() if sha(root / p) != h]
assert changed == ['programs/r1-cost-probe/src/r1_checkpoint_tests.rs'], changed
rec = read(packet / 'receipts/program-lib-path-fixed/receipt.json')
assert rec['exit_status'] == 0 and rec['swaps'] == 0
assert rec['limits'] == dict(zip(
    ['memory.high', 'memory.max', 'memory.swap.max', 'pids.max'],
    ['6442450944', '8589934592', '0', '64']))
stdout = (packet / 'receipts/program-lib-path-fixed/stdout.log').read_text()
assert '37 passed; 0 failed; 0 ignored' in stdout
for name in ['r15_release_stage1_rejects_occupied_and_wrong_size_without_writes',
             'r15_lifecycle_requires_recorded_signer_to_upload_or_seal',
             'r15_release_rejects_lifecycle_close_attempts_on_real_checkpoint_shape']:
    assert f'::{name} ... ok' in stdout
assert read(packet / 'receipts/program-lib/receipt.json')['exit_status'] == 127
remote = read(packet / 'source-validation.json')
assert remote['status'] == 'pass' and remote['mismatches'] == []
assert remote['checked_files'] == len(inputs)
assert remote['input_manifest_sha256'] == sha(packet / 'input-hashes.json')
reservation = read(packet / 'reservation-program-lib-path-fixed.json')
assert reservation['all_populated_scopes_bounded']
assert reservation['bounded_reserved_bytes'] + 8 * 2**30 <= reservation['safe_limit_bytes']
assets = {str(p.relative_to(packet)): {'sha256': sha(p), 'bytes': p.stat().st_size}
          for p in sorted(packet.rglob('*')) if p.is_file() and p.name != 'manifest.json'}
doc = root / 'docs/research/100bit-spend-path-20261013/design/R15-ADAPTER-WRITE-AUDIT-20261020.md'
manifest = dict(schema='r15-account-write-audit-v1',
                source_revision=rec['source_revision'],
                source_delta='Test-only additions in r1_checkpoint_tests.rs',
                freeze_revision=frozen['source_revision'],
                unchanged_freeze_inventory_entries=len(frozen['files']) - len(changed),
                changed_freeze_inventory_entries=changed,
                audit_sha256=sha(doc), input_files_checked=len(inputs),
                tests_passed=37, exit_status=rec['exit_status'],
                wall_seconds=rec['wall_seconds'], peak_rss_kib=rec['peak_rss_kib'],
                cgroup_memory_peak_bytes=rec['cgroup_memory_peak_bytes'],
                swaps=rec['swaps'], print_axioms='N/A: no Lean work', assets=assets)
if args.check:
    assert read(packet / 'manifest.json') == manifest, 'Packet/manifest drift'
else:
    (packet / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({k: manifest[k] for k in ['unchanged_freeze_inventory_entries',
      'input_files_checked', 'tests_passed', 'exit_status', 'audit_sha256']}))

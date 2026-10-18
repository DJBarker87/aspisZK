#!/usr/bin/env python3
"""Read/hash the two focused result receipts; never launch a build."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

E = Path(__file__).resolve().parent
B = E.parents[1]
sha = lambda b: hashlib.sha256(b).hexdigest()
summary = json.loads((E / 'SUMMARY.json').read_text())
archive = E / 'source-address-current-proof.tar.gz'
assert sha(archive.read_bytes()) == summary['archive_sha256']
with tarfile.open(archive) as t:
    files = {m.name: t.extractfile(m).read() for m in t if m.isfile()}
assert {n: sha(b) for n, b in files.items()} == summary['archive_members']
for target, attempt, count in [
        ('ExtractedSourceDigestAddresses', 'source-address-f', 19),
        ('ExtractedSourceCircleFrameBound', 'row25-frame-b', 1)]:
    prefix = 'runs/' + attempt + '/'
    receipt = json.loads(files[prefix + 'receipt.json'])
    assert receipt == summary['results'][target]
    assert receipt['exit_status'] == 0 and receipt['source_revision'] == summary['revision']
    assert receipt['process_swaps'] == 0 and receipt['cgroup_swap_current'] == '0'
    assert receipt['limits'] == {'memory.max': '8589934592',
                                 'memory.high': '6442450944', 'memory.swap.max': '0'}
    source = files['sources/' + target + '.lean']
    assert sha(source) == receipt['source_sha256']
    assert source == (B / 'lean/bridge-source-address-current-20261018' / (target + '.lean')).read_bytes()
    assert files[prefix + 'source.lean'] == source
    assert sha(files[prefix + 'input-manifest.json']) == receipt['input_manifest_sha256']
    manifest = json.loads(files[prefix + 'input-manifest.json'])
    assert manifest['sources'][target + '.lean'] == receipt['source_sha256']
    assert manifest['address_leaf_current_import_closure'] == summary['current_import_closure']
    log = files[prefix + 'lean.log'].decode()
    reports = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                         log, re.M)
    assert len(reports) == count
    assert 'sorryAx' not in log and ': error:' not in log and 'error(' not in log
    for name, axioms in reports:
        assert {s.strip() for s in axioms.split(',') if s.strip()} <= {
            'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    acquired = json.loads(files['runs/' + attempt + '-lock-acquired.json'])
    queue = json.loads(files['runs/' + attempt + '-queue.json'])
    assert queue['exit_status'] == 0 and queue['lock'] == '/tmp/aspis-r0-lean.lock'
    assert acquired['lock_held_by_parent_flock_until_child_exit']
    assert acquired['reserved_memory_max_bytes'] + acquired['own_memory_max_bytes'] < acquired['safe_limit_bytes']
libraries = {'backend', 'runtime', 'mathlib', 'aesop', 'batteries', 'Qq',
             'proofwidgets', 'plausible', 'LeanSearchClient', 'importGraph'}
for name, meta in summary['current_import_closure'].items():
    if meta.get('root') in libraries:
        continue
    assert sha(files['sources/' + name.replace('.', '/') + '.lean']) == meta['source_sha256'], name
    if 'build_receipt' in meta:
        assert sha(files['dependency-receipts/' + name + '.json']) == meta['build_receipt']['sha256']
for attempt in summary['failed_attempts']:
    prefix = 'runs/' + attempt + '/'
    receipt = json.loads(files[prefix + 'receipt.json'])
    assert receipt['exit_status'] == 1
    assert sha(files[prefix + 'source.lean']) == receipt['source_sha256']
for attempt, pid in summary['suppressed_attempts'].items():
    suppression = json.loads(files['runs/' + attempt + '/suppressed.json'])
    assert suppression['own_pid'] is None and suppression['external_pid'] == pid
    assert sha(files['runs/' + attempt + '/source.lean']) == suppression['source_sha256']
print(json.dumps({'status': 'PASS', 'focused_targets': 2, 'standard_axiom_reports': 20,
                  'current_dependency_entries': len(summary['current_import_closure']),
                  'shared_lead_lock': True, 'failed_and_suppressed_inputs_retained': True,
                  'builds_executed': False}))

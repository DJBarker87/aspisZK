#!/usr/bin/env python3
"""Verify source receipt, direct owner pins, and coherent namespace overlay."""
from pathlib import Path
import hashlib, json
P = Path(__file__).resolve().parent
REPO = P.parents[4]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def repo_path(p):
    q = REPO / p
    assert q.is_file(), p
    return q
for line in (P/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ',1)
    assert sha(P/name) == digest, name
r=json.loads((P/'receipts/receipt.json').read_text())
pre=json.loads((P/'receipts/preflight.json').read_text())
assert r['exit_status']==0 and r['swap_bytes']==0 and r['peak_rss_bytes']==3691544576
assert r['axioms']==['propext','Classical.choice','Quot.sound']
source=P/'sources/S4V10InstalledToLimbsSlotV1.lean'
assert sha(source)==r['source_sha256']==pre['source_sha256']
assert sha(Path(r['object_path']))==r['object_sha256']
assert sha(Path(r['compiler']))==r['compiler_sha256']
assert not list(P.rglob('*.olean'))
for name,pin in r['direct_imports'].items():
    assert sha(repo_path(pin['source_path']))==pin['source_sha256'], name+' source'
    assert sha(Path(pin['object_path']))==pin['object_sha256'], name+' object'
ov=json.loads((P/'receipts/namespace-overlay.json').read_text())
assert len(ov['entries'])==3
for entry in ov['entries']:
    resolved=Path(entry['resolved_path'])
    assert resolved.is_file() and sha(resolved)==entry['sha256']
    assert sha(Path('/tmp/s4-to-limbs-current-namespace-overlay')/entry['module_path'])==entry['sha256']
    assert sha(repo_path(entry['source_path']))==entry['source_sha256']
log=(P/'receipts/compile.log').read_text()
assert 'literal_to_limbs_installed' in log and 'depends on axioms: [propext,' in log
assert '12.12 real' in (P/'receipts/time.log').read_text()
print('PASS: focused Lean source, object, compiler, and direct import receipt')
print('PASS: exact coherent Types/FunsOpsV4/ToLimbsBody namespace overlay')
print('PASS: generated transparent method is tied to the concrete installed head slot')

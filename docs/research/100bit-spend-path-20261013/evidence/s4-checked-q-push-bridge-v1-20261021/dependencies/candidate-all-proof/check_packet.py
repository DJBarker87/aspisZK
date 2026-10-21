#!/usr/bin/env python3
from pathlib import Path
import hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
h = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
pkt = json.loads((HERE / 'proof-packet.json').read_text())
assert pkt['schema'] == 'focused-extractor-proof-packet-v1'
assert pkt['modules']
for name, m in pkt['modules'].items():
    source = ROOT / m['source']
    receipt = ROOT / m['receipt']
    assert source.is_file() and h(source) == m['source_sha256'], name
    assert receipt.is_file()
    r = json.loads(receipt.read_text())
    assert r['phase'] == 'proof-v6' and r['exit_status'] == 0
    assert r['targets'][0]['exit_status'] == 0
    assert r['limits'] == {'memory.high':'1610612736','memory.max':'2147483648','memory.swap.max':'0'}
    assert m['axioms'] == ['propext','Classical.choice','Quot.sound']
    log = (HERE / 'target.log').read_text()
    assert 'depends on axioms: [propext,' in log and 'sorryAx' not in log
    assert m['object_sha256'] == 'fa3107f4c61e8135f11d0d7a53a1ee29354817521c3ca8726944c771bf05b876'
for key, info in pkt['inputs'].items():
    p = ROOT / info['path']
    assert p.is_file() and h(p) == info['sha256'], key
for name, owner in pkt['direct_import_source_map'].items():
    p = ROOT / owner['source'] if (ROOT / owner['source']).is_file() else Path(owner['source'])
    assert p.is_file() and h(p) == owner['source_sha256'], name

# The only generated-source adaptation strips the two forbidden resource-option lines.
for base in ('Types','Funs'):
    generated = ROOT / 'source-cut/emitted/generated/AspisR1CheckedQCandidateV1' / f'{base}.lean'
    adapted = HERE / f'{base}.lean'
    original = generated.read_text()
    expected = original.replace('set_option maxHeartbeats 1000000\n','').replace('set_option maxRecDepth 2048\n','')
    assert expected == adapted.read_text(), base

assert 'generated_from_limbs_eq_existing_all_model' in (HERE/'CandidateAllEquivalence.lean').read_text()
assert not any(p.suffix == '.olean' for p in ROOT.rglob('*') if p.is_file())
print('PASS: source/input/import pins, resource receipt, standard-only axioms, and exact generated-source adaptation')

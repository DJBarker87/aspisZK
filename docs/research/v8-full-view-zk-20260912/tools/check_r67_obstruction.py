#!/usr/bin/env python3
"""Audit a diagnosed source-tool obstruction, not a passing privacy gate."""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r67-circle-source'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(path,exit):
    s=path.read_text();assert f'\tExit status: {exit}' in s and '\tSwaps: 0' in s
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':exit,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
      'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
original=e/'extraction-failure';eta=e/'eta-extraction'
stage=root/'evidence/r63-generated-inverse/source/r18-stage.json'
pins=json.loads(stage.read_text())['files'];assert len(pins)==197
names=['field.rs','circle.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']
for n in names:assert sha(original/'source'/n)==pins['crates/aspis-core/src/'+n]
for n in names:
    if n!='r24_guarded_qm.rs':assert sha(eta/'source'/n)==sha(original/'source'/n)
for n in ['Cargo.toml','lib.rs']:
    assert sha(original/'source'/n)==sha(eta/'source'/n)==sha(root/'tools/r67-circle-extraction'/n)
before=(original/'source/r24_guarded_qm.rs').read_text()
after=(eta/'source/r24_guarded_qm.rs').read_text()
assert before.count('.map(u64::from)')==2
assert after==before.replace('.map(u64::from)','.map(|value| u64::from(value))')
assert sha(eta/'original/r24_guarded_qm.rs')==sha(original/'source/r24_guarded_qm.rs')
normal=json.loads((eta/'normalization.json').read_text())
assert normal['before_sha256']==sha(original/'source/r24_guarded_qm.rs')
assert normal['after_sha256']==sha(eta/'source/r24_guarded_qm.rs') and normal['sites']==2
for n,h in json.loads((eta/'pins.json').read_text()).items():assert sha(eta/n)==h,n
results={}
for folder,code in [(original,2),(eta,0)]:
    env=json.loads((folder/'environment.json').read_text())
    assert env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true' and env['RUSTUP_TOOLCHAIN']=='nightly-2026-06-01'
    cmds=json.loads((folder/'commands.json').read_text())
    assert [c['label'] for c in cmds]==['lock','extract','translate']
    assert [c['exit'] for c in cmds]==[0,0,code]
    assert all(x in cmds[1]['command'] for x in ['--release','--locked','--offline','crate::circle_probe'])
    assert not json.loads((folder/'R67Circle.llbc').read_text())['has_errors']
    results[folder.name]={label:metrics(folder/(label+'.log'),code if label=='translate' else 0)
      for label in ['lock','extract','translate']}
assert 'SymbolicToPureTypes.ml, line 444' in (original/'translate.log').read_text()
assert 'can_fail' in (e/'translator-source/SymbolicToPureTypes.ml').read_text().splitlines()[443]
templates=list((eta/'generated/AspisR67Circle').glob('*External_Template.lean'));assert len(templates)==2
holes=[]
for template in templates:holes+=re.findall(r'^axiom ([\w.]+)',template.read_text(),re.M)
expected=[
 'core.iter.adapters.chain.Chain','core.array.Array.map',
 'core.iter.traits.iterator.Iterator.any.default','core.iter.traits.iterator.Iterator.chain.default',
 'core.iter.adapters.chain.Chain.Insts.CoreIterTraitsIteratorIterator.next',
 'core.option.Option.ok_or','core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any']
assert set(holes)==set(expected) and len(holes)==7
meta=json.loads((eta/'generated/translation.json').read_text())
assert len(meta['functions'])==49 and sum(f['is_local'] for f in meta['functions'])==43
assert sum(f['is_opaque'] for f in meta['functions'])==6
for src in (root/'lean').rglob('*.lean'):
    assert 'AspisR67Circle' not in src.read_text(), 'diagnostic output imported into accepted proof tree'
record=json.loads((e/'collection.json').read_text())
assert record['aeneas_sha256']=='e3e6e658ad26168421eb37627561930c1e13afa978f77b214a1201d9c4faa813'
assert record['charon_sha256']=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
assert not record['accepted_as_source_proof'] and record['no_new_Lean_compilation']
receipt={'base_revision':record['base_revision'],'results':results,'unchanged_source_files_original':5,
 'source_stage_pins':197,'eta_expanded_sites':2,'diagnostic_external_axioms':expected,
 'eta_translation_completed':True,'accepted_source_bridge':False,'new_Lean_theorems':0,
 'new_Rust_differential_test':False,'eta_normalization_formally_source_verified':False,
 'runtime_changed':False,'full_privacy':False,'full_soundness':False,
 'retained_cu':[1497377,1498764], 'actual_1M_gate_passed':False,
 'first_remaining':'source-grounded, axiom-free array.map/iterator chain+any/Option.ok_or support, plus pure-function-item lowering or verified eta normalization; then guarded QM31/circle execution',
 'requested_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}}
sources=[stage,root/'evidence/r66-quartic-inverse/receipt.json',
 *[root/'tools'/n for n in ['extract_r64_field.py','extract_r67_circle.py','extract_r67_circle_eta.py','collect_r67_obstruction.py','check_r67_obstruction.py']],
 *list((root/'tools/r67-circle-extraction').iterdir())]
source_pins={str(p.relative_to(repo)):sha(p) for p in sources if p.is_file()}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(source_pins,indent=2)+'\n')
    manifest={str(p.relative_to(e)):sha(p) for p in sorted(e.rglob('*')) if p.is_file() and p.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt
assert json.loads((e/'SOURCE_PINS.json').read_text())==source_pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(p.relative_to(e)) for p in e.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'evidence_audit':'PASS','source_bridge':'OPEN','artifacts':len(manifest),
 'external_axioms_rejected':7,'new_Lean_theorems':0,'full_privacy':False},indent=2))

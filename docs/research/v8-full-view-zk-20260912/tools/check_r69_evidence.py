#!/usr/bin/env python3
"""Audit the measured fixed-arity source and exact, template-free extraction.
Passing this audit is not a complete field, circle, privacy or soundness proof.
"""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r69-explicit-source';run=e/'runtime';extract=e/'extraction'
parent=root/'evidence/r62-ordinary/gather-checked'
base='265a251ecfbff6cd971a32eccd72cff552786885'
ex='docs/research/v8-no-work-100-20260907/experiments/'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def metrics(path,exit=0):
    s=path.read_text();assert re.findall(r'\tExit status: (\d+)',s)[-1]==str(exit)
    assert all(x=='0' for x in re.findall(r'\tSwaps: (\d+)',s))
    t=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[-1]
    return {'exit':exit,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
            'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[-1])}
pm=read(parent/'r18-stage.json');m=read(run/'r18-stage.json')
assert len(pm['files'])==197 and len(m['files'])==202
assert m['r69_explicit_product']['base_revision']==base
assert m['r69_explicit_product']['control_manifest_sha256']==sha(parent/'r18-stage.json')
changed={n for n,h in m['files'].items()if pm['files'].get(n)!=h}
expected={'crates/aspis-core/src/r24_guarded_qm.rs',ex+'performance-host/Cargo.toml',ex+'r69_explicit_check.rs'}
expected|={ex+'r69_reference/'+n for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']}
assert changed==expected and set(pm['files'])<=set(m['files'])
for n in changed:assert sha(run/'source'/n)==m['files'][n],n
for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    assert sha(run/'source'/(ex+'r69_reference/'+n))==pm['files']['crates/aspis-core/src/'+n]
assert sha(root/'tools/r69_explicit_product.rs')==m['files']['crates/aspis-core/src/r24_guarded_qm.rs']
assert sha(root/'tools/r69_explicit_check.rs')==m['files'][ex+'r69_explicit_check.rs']
for n in ['field.rs','circle.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    assert sha(extract/'source'/n)==m['files']['crates/aspis-core/src/'+n]
assert not (extract/'normalization.json').exists()
for n,h in read(extract/'pins.json').items():assert sha(extract/n)==h,n
assert sha(e/'stdlib/option.rs')==sha(root/'evidence/r67-circle-source/stdlib-source/option.rs')
env=read(extract/'environment.json')
assert env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true' and env['RUSTUP_TOOLCHAIN']=='nightly-2026-06-01'
commands=read(extract/'commands.json')
assert [c['exit']for c in commands]==[0,0,0]
assert all(v in commands[1]['command'] for v in ['--release','--locked','--offline','core::option'])
assert not read(extract/'R69Explicit.llbc')['has_errors']
meta=read(extract/'generated/translation.json')
assert len(meta['functions'])==38 and not any(f['is_opaque'] for f in meta['functions'])
assert len(meta['types'])==6
generated=extract/'generated/AspisR69Explicit'
assert sorted(f.name for f in generated.iterdir())==['Funs.lean','Types.lean']
for n in ['Types','Funs']:
    old=(generated/(n+'.lean')).read_text()
    new=(root/'lean/AspisR69Explicit'/(n+'.lean')).read_text()
    marker='namespace AspisR69Explicit\n'
    assert new.split(marker,1)[1]==old.split(marker,1)[1]
    assert 'TraversalRuntime' not in new and 'External' not in new
    assert not re.search(r'\b(axiom|sorry|admit)\b',new)
logs={}
for kind,names in [('host',['product-compile','product-check','ordinary-compile','ordinary-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    env=read(run/f'r24-{kind}-a/environment.json')
    assert env['source_manifest_sha256']==sha(run/'r18-stage.json')
    assert env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for name in names:logs[f'{kind}/{name}']=metrics(run/f'r24-{kind}-a'/(name+'.log'))
product=(run/'r24-host-a/product-check.log').read_text()
for marker in ['canonical_pairs=265536','boundary_pairs=65536','random_pairs=200000',
               'frozen_source=true independent_u128=true prepared_and_checked_dot=true',
               'invalid_constructor_cases=40 fallback_retained=true']:assert marker in product
wire=read(run/'r24-host-a/wire-controls/results.json')
assert len(wire['cases'])==3281 and all(x['exit']==0 for x in wire['cases'])
assert sum(x['checked_rejection']for x in wire['cases'])==3280
for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (run/f'r24-host-a/world{w}.log').read_text()
build=(run/'r24-sbf-a/compile.log').read_text()
assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
svm=read(run/'r24-svm-a/receipt.json');oldsvm=read(parent/'r24-svm-a/receipt.json')
assert svm['full_verifier'] and not svm['instrumented']
assert svm['source_manifest_sha256']==sha(run/'r18-stage.json')
assert svm['elf_sha256']==read(run/'r24-sbf-a/environment.json')['elf_sha256']==read(e/'collection.json')['observed_elf_sha256']
assert svm['driver_sha256']==oldsvm['driver_sha256']
cu=[]
assert len(svm['runs'])==2
for i,r in enumerate(svm['runs']):
    assert r['world']==i and r['proof_sha256']==oldsvm['runs'][i]['proof_sha256']
    assert len(r['results'])==4
    for x in r['results']:
        assert x['heap_bytes']==262144 and x['unchanged_accounts']
        if x['cu_limit']==1000000:
            assert x['resource_failure'] and not x['accepted'] and not x['custom_rejection'] and x['cu']==1000000
        else:
            assert x['cu_limit']==100000000 and not x['resource_failure']
            if x['case']=='honest':assert x['accepted'];cu.append(x['cu'])
            else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted'] and x['error']=='InstructionError(0, Custom(6))'
assert cu==[1495663,1497050]
targets=['AspisR69Explicit/Types','AspisR69Explicit/Funs','AspisV8R19/ExplicitGuard']
records=read(e/'final/metadata.json');assert len(records)==313
assert [r['target_name'] for r in records[-3:]]==targets
for r in records[-3:]:
    assert r['exit']==0 and r['base_revision']==base and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))
    logs[r['target_name']]=metrics(e/'final'/(Path(r['target_name']).name+'.log'))
s=(e/'final/ExplicitGuard.log').read_text();assert 'sorryAx' not in s
audits=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",s)
assert len(audits)==7
for _,names in audits:assert {v.strip() for v in names.split(',')if v.strip()}<={'propext','Classical.choice','Quot.sound'}
res=read(e/'final/resources.json')
assert {k:res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
    'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
diagnostics={}
for name in ['chain-a','chain-b','array-a','array-b']:
    folder=e/name
    assert [c['exit']for c in read(folder/'commands.json')]==[0,0,2]
    assert not read(folder/'R69Circle.llbc')['has_errors']
    diagnostics[name]={n:metrics(folder/(n+'.log'),2 if n=='translate'else 0)for n in ['lock','extract','translate']}
    log=(folder/'translate.log').read_text()
    assert ('SymbolicToPureTypes.ml, line 1047' in log if name.startswith('chain') else
            ('MaybeDangling' if name=='array-a' else 'ManuallyDrop')in log)
receipt={'base_revision':base,'source_pins':202,'cu':cu,'previous_cu':[1497377,1498764],
    'saving_each_fixture':1714,'selected_runtime_candidate':True,'actual_1M_gate_passed':False,
    'elf_sha256':svm['elf_sha256'],'logs':logs,'diagnostics':diagnostics,
    'extraction':{n:metrics(extract/(n+'.log'))for n in ['lock','extract','translate']},
    'source_normalization_used':False,'external_templates':0,'generated_functions':38,
    'new_theorems':4,'generated_definition_audits':3,'new_axioms':0,
    'protocol_changed':False,'canonical_product_execution_proved':False,
    'circle_execution_proved':False,'full_privacy':False,'full_soundness':False,
    'first_remaining':'For all canonical QM31 pairs, prove the extracted fixed-arity guarded product returns the canonical exact product without Result failure; then compose the existing inverse with circle and bounded sampler execution.',
    'requested_scopes':{'host':'5G/7G','sbf':'12G/16G','svm':'5G/7G','lean':'5G/7G','MemorySwapMax':0,'TasksMax':128}}
paths=[root/'lean'/(t+'.lean')for t in targets]
paths += [root/'tools'/n for n in ['check_r69_evidence.py','collect_r69_evidence.py',
    'stage_r69_explicit.py','r69_explicit_product.rs','r69_explicit_check.rs','run_r69_full.py',
    'extract_r69_library.py','extract_r69_explicit.py','extract_r64_field.py','run_r69_lean.py',
    'run_r68_lean.py','run_r64_lean.py','run_r63_lean.py','run_r23_full.py','build_r20_sbf.py','check_r19_wire_controls.py']]
paths += [parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',root/'evidence/r67-circle-source/MANIFEST.json']
pins={str(f.relative_to(repo)):sha(f)for f in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert read(e/'receipt.json')==receipt and read(e/'SOURCE_PINS.json')==pins
manifest=read(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'audit':'PASS','cu':cu,'templates':0,'new_theorems':4,'full_privacy':False,'artifacts':len(manifest)},indent=2))

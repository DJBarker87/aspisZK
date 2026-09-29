#!/usr/bin/env python3
"""Validate the arithmetic candidate without confusing local tests with privacy."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r56-partial-product';parent=root/'evidence/r55-opening-decode/marker'
base='ad3e1634e711f1c1aeaf97271c4934eb07697b5c'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^error(?:\[|:)',s,re.M) and 'sorryAx' not in s,p
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
m=json.loads((e/'r18-stage.json').read_text());pm=json.loads((parent/'r18-stage.json').read_text())
assert len(m['files'])==188 and len(pm['files'])==183
meta=m['r56_partial_product'];assert meta['base_revision']==base
assert meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
assert meta['guard_and_fallback_unchanged'] and meta['final_reducer_unchanged'] and not meta['protocol_changed']
ex='docs/research/v8-no-work-100-20260907/experiments/';helper='crates/aspis-core/src/r24_guarded_qm.rs'
refs=['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']
changed={n for n,h in m['files'].items()if pm['files'].get(n)!=h}
assert changed=={helper,ex+'performance-host/Cargo.toml',ex+'r56_product_check.rs',*[ex+'r56_reference/'+n for n in refs]}
for n in changed:assert sha(e/'source'/n)==m['files'][n]
for n in refs:assert m['files'][ex+'r56_reference/'+n]==pm['files']['crates/aspis-core/src/'+n]
assert sha(root/'tools/r56_partial_product.rs')==m['files'][helper]
assert sha(root/'tools/r56_product_check.rs')==m['files'][ex+'r56_product_check.rs']
old=(e/'source'/(ex+'r56_reference/r24_guarded_qm.rs')).read_text();new=(root/'tools/r56_partial_product.rs').read_text()
assert old[old.index('fn r24_canonical_mul'):old.index('    let reduce=')]==new[new.index('fn r24_canonical_mul'):new.index('    // A single fold')]
assert old[old.index('        (a*g)'):]==new[new.index('        (a*g)'):]
logs={}
for kind,names in [('host',['r56-product-check-compile','r56-product-check','r24-dot-check-compile',
    'r24-dot-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    d=e/f'r24-{kind}-a';env=json.loads((d/'environment.json').read_text())
    assert env['source_manifest_sha256']==sha(e/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for n in names:logs[f'{kind}/{n}']=metrics(d/(n+'.log'))
product=(e/'r24-host-a/r56-product-check.log').read_text()
for x in ['canonical_pairs=265536','boundary_pairs=65536','random_pairs=200000','frozen_source=true',
    'independent_u128=true','prepared_and_checked_dot=true','invalid_constructor_cases=24','fallback_retained=true']:assert x in product
dot=(e/'r24-host-a/r24-dot-check.log').read_text()
for x in ['cases=600192','canonical_vectors=200064','cases=576','noncanonical_cases=7272']:assert x in dot,x
wire=json.loads((e/'r24-host-a/wire-controls/results.json').read_text())
assert len(wire['cases'])==3281 and sum(x['checked_rejection']for x in wire['cases'])==3280
assert all(x['exit']==0 for x in wire['cases'])
for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (e/f'r24-host-a/world{w}.log').read_text()
build=(e/'r24-sbf-a/compile.log').read_text()
assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
svm=json.loads((e/'r24-svm-a/receipt.json').read_text());oldsvm=json.loads((parent/'r24-svm-a/receipt.json').read_text())
assert svm['source_manifest_sha256']==sha(e/'r18-stage.json')
assert svm['elf_sha256']==json.loads((e/'r24-sbf-a/environment.json').read_text())['elf_sha256']
assert svm['driver_sha256']==oldsvm['driver_sha256'] and svm['full_verifier'] and not svm['instrumented']
cu=[];baseline=[]
assert len(svm['runs'])==2
for i,r in enumerate(svm['runs']):
    assert r['world']==i and r['proof_sha256']==oldsvm['runs'][i]['proof_sha256'] and len(r['results'])==4
    baseline.append(next(x['cu']for x in oldsvm['runs'][i]['results']if x['case']=='honest' and x['cu_limit']==100000000))
    for x in r['results']:
        assert x['heap_bytes']==262144 and x['unchanged_accounts']
        if x['cu_limit']==1000000:
            assert x['resource_failure'] and not x['custom_rejection'] and not x['accepted'] and x['cu']==1000000
        else:
            assert x['cu_limit']==100000000 and not x['resource_failure']
            if x['case']=='honest':assert x['accepted'];cu.append(x['cu'])
            else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted']
assert svm['runs'][0]['proof_sha256']!=svm['runs'][1]['proof_sha256']
trace=json.loads((e/'full-trace/analysis.json').read_text());tr=json.loads((e/'full-trace/receipt.json').read_text())
assert trace['elf_sha256']==tr['elf_sha256']==svm['elf_sha256']
assert trace['exact_text_match'] and tr['clean_cu_equal'] and trace['cu']==tr['result']['cu']==cu[0]
trace_time=metrics(e/'full-trace/run.log')
records=json.loads((e/'lean-b/metadata.json').read_text());assert len(records)==288
pins={}
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
assert records[-1]['target_name']=='AspisV8R19/PartialProduct' and records[-1]['base_revision']==base
lean=metrics(e/'lean-b/PartialProduct.log');s=(e/'lean-b/PartialProduct.log').read_text()
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s)
assert len(axioms)+s.count('does not depend on any axioms')==9
assert all(set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for x in axioms)
src=(root/'lean/AspisV8R19/PartialProduct.lean').read_text()
assert len(re.findall(r'^theorem ',src,re.M))==9 and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
initial=metrics(e/'lean-a/PartialProduct.log')
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text())
def normalized(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x for x in t['functions']}
before=normalized(oldtrace);after=normalized(trace)
assert set(before)==set(after)
deltas={n:before[n]['instructions']-after[n]['instructions']for n in before
        if before[n]['instructions']!=after[n]['instructions']}
assert deltas=={'aspis_core::field::QM31::mul':17398,
    'aspis_core::field::r25_checked_dot':6176,'aspis_core::field::PreparedQm31Multiplier::mul':2492}
assert all(before[n]['entries']==after[n]['entries']for n in before)
receipt={'base_revision':base,'source_pins':188,'cu':cu,'baseline_cu':baseline,'saved_cu':[a-b for a,b in zip(baseline,cu)],
    'selected':all(b<a for a,b in zip(baseline,cu)),'actual_1M_gate_passed':False,
    'logs':logs,'trace':trace_time,'executed_instructions':trace['executed_instructions'],
    'executed_instruction_reduction':oldtrace['executed_instructions']-trace['executed_instructions'],
    'exclusive_function_instruction_reductions':deltas,
    'Lean':lean,'initial_six_lemma_compile':initial,'axioms_audits':9,'new_theorems':9,'final_cache_objects':288,
    'resources':{'RustHigh':'5G','RustMax':'7G','LeanHigh':'3G','LeanMax':'5G','runtimeHigh':'2G','runtimeMax':'3G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,
    'numerical_source_privacy_bound':None}
names=['r56_partial_product.rs','r56_product_check.rs','stage_r56_product.py','run_r56_full.py','run_r56_lean.py',
    'collect_r56_evidence.py','check_r56_evidence.py','run_r23_full.py','run_r50_lean.py','build_r20_sbf.py',
    'check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
for path in [root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',parent/'full-trace/analysis.json']:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),**{k:receipt[k]for k in
    ['cu','saved_cu','selected','new_theorems','actual_1M_gate_passed','full_privacy']}},indent=2))

#!/usr/bin/env python3
"""R59 exact raw-formula delta, arithmetic proofs and full execution gate."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r59-partial-dot';parent=root/'evidence/r58-tag-base'
base='6af7c8384ccea9dce41e16075cd29f77179bd8a0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^error(?:\[|:)',s,re.M) and 'sorryAx' not in s,p
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
m=json.loads((e/'r18-stage.json').read_text());pm=json.loads((parent/'r18-stage.json').read_text())
assert len(m['files'])==len(pm['files'])==195 and set(m['files'])==set(pm['files'])
meta=m['r59_partial_dot'];assert meta['base_revision']==base and meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
assert meta['input_guards_unchanged'] and meta['raw_formula_unchanged'] and meta['four_accumulators'] and meta['max_terms']==4096 and not meta['protocol_changed']
helper='crates/aspis-core/src/r25_checked_dot.rs'
assert {n for n,h in m['files'].items()if pm['files'][n]!=h}=={helper}
assert sha(e/'source'/helper)==m['files'][helper]
raw=(root/'tools/r56_partial_product.rs').read_text();assert sha(root/'tools/r56_partial_product.rs')==pm['files']['crates/aspis-core/src/r24_guarded_qm.rs']
raw=raw.replace('fn r24_canonical_mul(left:QM31,right:QM31)->Option<QM31>', 'fn r59_raw_product(left:QM31,right:QM31)->Option<[u64;4]>')
old='].map(M31::reduce_u64);\n    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})'
assert raw.count(old)==1;raw=raw.replace(old,'];\n    Some(out)')
assert (e/'source'/helper).read_text()=='// Raw outputs stay private to this checked dot.\n'+raw+'\n'+(root/'tools/r59_partial_dot.rs').read_text()
logs={}
for kind,names in [('host',['r56-product-check-compile','r56-product-check','r24-dot-check-compile','r24-dot-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    d=e/f'r24-{kind}-a';env=json.loads((d/'environment.json').read_text())
    assert env['source_manifest_sha256']==sha(e/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for n in names:logs[f'{kind}/{n}']=metrics(d/(n+'.log'))
prod=(e/'r24-host-a/r56-product-check.log').read_text();dot=(e/'r24-host-a/r24-dot-check.log').read_text()
for x in ['canonical_pairs=265536','boundary_pairs=65536','random_pairs=200000','frozen_source=true','independent_u128=true','prepared_and_checked_dot=true','invalid_constructor_cases=24','fallback_retained=true']:assert x in prod
for x in ['cases=600192','differential_cases=576','noncanonical_cases=7272','length_errors=2','max_terms=4096']:assert x in dot
wire=json.loads((e/'r24-host-a/wire-controls/results.json').read_text())
assert len(wire['cases'])==3281 and sum(x['checked_rejection']for x in wire['cases'])==3280 and all(x['exit']==0 for x in wire['cases'])
for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (e/f'r24-host-a/world{w}.log').read_text()
build=(e/'r24-sbf-a/compile.log').read_text()
assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
svm=json.loads((e/'r24-svm-a/receipt.json').read_text());oldsvm=json.loads((parent/'r24-svm-a/receipt.json').read_text())
assert svm['source_manifest_sha256']==sha(e/'r18-stage.json')
assert svm['elf_sha256']==json.loads((e/'r24-sbf-a/environment.json').read_text())['elf_sha256']
assert svm['driver_sha256']==oldsvm['driver_sha256'] and svm['full_verifier'] and not svm['instrumented']
cu=[];baseline=[];assert len(svm['runs'])==2
for i,r in enumerate(svm['runs']):
    assert r['world']==i and r['proof_sha256']==oldsvm['runs'][i]['proof_sha256'] and len(r['results'])==4
    baseline.append(next(x['cu']for x in oldsvm['runs'][i]['results']if x['case']=='honest' and x['cu_limit']==100000000))
    for x in r['results']:
        assert x['heap_bytes']==262144 and x['unchanged_accounts']
        if x['cu_limit']==1000000:assert x['resource_failure'] and not x['custom_rejection'] and not x['accepted'] and x['cu']==1000000
        else:
            assert x['cu_limit']==100000000 and not x['resource_failure']
            if x['case']=='honest':assert x['accepted'];cu.append(x['cu'])
            else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted']
assert svm['runs'][0]['proof_sha256']!=svm['runs'][1]['proof_sha256']
trace=json.loads((e/'full-trace/analysis.json').read_text());tr=json.loads((e/'full-trace/receipt.json').read_text())
assert trace['elf_sha256']==tr['elf_sha256']==svm['elf_sha256']
assert trace['exact_text_match'] and tr['clean_cu_equal'] and trace['cu']==tr['result']['cu']==cu[0]
trace_time=metrics(e/'full-trace/run.log')
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==291;pins={}
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
assert records[-1]['target_name']=='AspisV8R19/PartialDot' and records[-1]['base_revision']==base
lean=metrics(e/'lean/PartialDot.log');s=(e/'lean/PartialDot.log').read_text()
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s);assert len(axioms)==8
assert all(set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for x in axioms)
src=(root/'lean/AspisV8R19/PartialDot.lean').read_text()
assert len(re.findall(r'^theorem ',src,re.M))==8 and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text())
def normalized(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x['instructions']for x in t['functions']}
before=normalized(oldtrace);after=normalized(trace)
deltas={n:before.get(n,0)-after.get(n,0)for n in before.keys()|after.keys()if before.get(n,0)!=after.get(n,0)}
assert sum(deltas.values())==oldtrace['executed_instructions']-trace['executed_instructions']==baseline[0]-cu[0]
assert deltas=={'aspis_core::field::r25_checked_dot':23664}
callers=json.loads((e/'control-callers.json').read_text())
assert callers['elf_sha256']==oldsvm['elf_sha256'] and callers['trace_analysis_sha256']==sha(parent/'full-trace/analysis.json') and not callers['source_line_attribution']
for name in ['aspis_core::field::QM31::mul','aspis_core::field::PreparedQm31Multiplier::mul','aspis_core::field::r25_checked_dot']:
    rows=[x for x in callers['calls']if x['callee']==name];old=next(x for x in oldtrace['functions']if re.sub(r'::h[0-9a-f]+$','',x['name'])==name)
    assert sum(x['calls']for x in rows)==old['entries'] and sum(x['exclusive_instructions']for x in rows)==old['instructions']
receipt={'base_revision':base,'source_pins':195,'cu':cu,'baseline_cu':baseline,'saved_cu':[a-b for a,b in zip(baseline,cu)],
    'selected':all(b<a for a,b in zip(baseline,cu)),'actual_1M_gate_passed':False,'logs':logs,'trace':trace_time,
    'executed_instructions':trace['executed_instructions'],'executed_instruction_reduction':oldtrace['executed_instructions']-trace['executed_instructions'],
    'exclusive_function_instruction_reductions':deltas,'Lean':lean,'axioms_audits':8,'new_theorems':8,'final_cache_objects':291,
    'resources':{'RustHigh':'5G','RustMax':'7G','LeanHigh':'3G','LeanMax':'5G','runtimeHigh':'2G','runtimeMax':'3G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['r59_partial_dot.rs','stage_r59_dot.py','run_r59_full.py','run_r59_lean.py','r59_callers.py','collect_r59_evidence.py','check_r59_evidence.py',
    'r56_partial_product.rs','run_r23_full.py','run_r50_lean.py','build_r20_sbf.py','check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
for path in [root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',parent/'full-trace/analysis.json']:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');(e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text());assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),**{k:receipt[k]for k in ['cu','saved_cu','selected','new_theorems','actual_1M_gate_passed','full_privacy']}},indent=2))

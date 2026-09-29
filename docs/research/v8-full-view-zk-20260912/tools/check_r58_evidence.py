#!/usr/bin/env python3
"""R58 source-delta, arithmetic leaves, malformed-input and complete-SVM gate."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r58-tag-base';parent=root/'evidence/r57-selector-gather'
base='e6e2015650ba4104da3797e4c375591ba29e92c0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^error(?:\[|:)',s,re.M) and 'sorryAx' not in s,p
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
m=json.loads((e/'r18-stage.json').read_text());pm=json.loads((parent/'r18-stage.json').read_text())
assert len(m['files'])==195 and len(pm['files'])==193
meta=m['r58_tag'];assert meta['base_revision']==base and meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
assert meta['tag_base']==1124073472 and meta['maximum_delta']==135 and meta['paired_pattern_correction'] and not meta['protocol_changed']
ex='docs/research/v8-no-work-100-20260907/experiments/';mod='crates/aspis-statement/src/pool_v1/'
changed={n for n,h in m['files'].items()if pm['files'].get(n)!=h}
assert set(pm['files'])<=set(m['files'])
assert changed=={mod+'pair_forest_copy_terminal.rs',mod+'r58_tag_base.rs',ex+'performance-host/Cargo.toml',ex+'r58_tag_check.rs'}
for n in changed:assert sha(e/'source'/n)==m['files'][n]
assert sha(root/'tools/r58_tag_base.rs')==m['files'][mod+'r58_tag_base.rs']
s=(parent/'source'/(mod+'pair_forest_copy_terminal.rs')).read_text()
tag=function(s,'fn copy_tag_coordinate_dot(');finish=function(s,'fn finish_selector_tensor_basis(')
reference=function(s,'pub(crate) fn r57_reference_evaluate(')
condition='all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")'
brace=tag.index('{')
new=tag[:brace+1]+f'\n    #[cfg({condition})]\n    {{ r58_tag_delta(coordinate, selectors) }}\n    #[cfg(not({condition}))]\n    {{'+tag[brace+1:-1]+'\n    }\n}'
brace=finish.index('{')
shift=f'''\n    #[cfg({condition})]
    let mut shifted_patterns = *patterns;
    #[cfg({condition})]
    for pattern in &mut shifted_patterns {{ pattern.c0.a = pattern.c0.a.add(M31(R58_TAG_BASE)); }}
    #[cfg({condition})]
    let patterns = &shifted_patterns;
'''
s=s.replace(tag,new).replace(finish,finish[:brace+1]+shift+finish[brace+1:])
s=s.replace(reference,reference.replace('finish_selector_tensor_basis(', 'r58_reference_finish('))
cfg=f'#[cfg(all(not(v8_performance_sbf), {condition}))]'
s+='\n'+cfg+'\n'+tag.replace('fn copy_tag_coordinate_dot(','fn r58_reference_tag_dot(')+'\n'
s+='\n'+cfg+'\n'+finish.replace('fn finish_selector_tensor_basis(','fn r58_reference_finish(').replace('copy_tag_coordinate_value(','r58_reference_tag_value(')+'\n'
s+='\n'+cfg+'''
fn r58_reference_tag_value(_scratch:&[QM31],coordinate:usize,selectors:&Selectors)->QM31 {
    r58_reference_tag_dot(coordinate,selectors)
}
'''
s+=f'#[cfg({condition})]\ninclude!("r58_tag_base.rs");\n'
assert (e/'source'/(mod+'pair_forest_copy_terminal.rs')).read_text()==s
logs={}
for kind,names in [('host',['tag-compile','tag-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    d=e/f'r24-{kind}-a';env=json.loads((d/'environment.json').read_text())
    assert env['source_manifest_sha256']==sha(e/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for n in names:logs[f'{kind}/{n}']=metrics(d/(n+'.log'))
control=(e/'r24-host-a/tag-check.log').read_text()
for x in ['source_terms=544','weight_checks=70720','scratch_and_full_lane_cases=512','original_tag_and_finish=true',
    'coordinate_checks=9600','finish_checks=640','omitted_base_negative_cases=2978','four_limb_basis=true','source_reference=true']:assert x in control
wire=json.loads((e/'r24-host-a/wire-controls/results.json').read_text())
assert len(wire['cases'])==3281 and sum(x['checked_rejection']for x in wire['cases'])==3280 and all(x['exit']==0 for x in wire['cases'])
for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (e/f'r24-host-a/world{w}.log').read_text()
build=(e/'r24-sbf-a/compile.log').read_text()
assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
failed=(e/'feature-preflight-failure/r24-sbf-a/compile.log').read_text()
assert 'cannot find function `finish_pattern_basis_values`' in failed and '\tExit status: 1' in failed
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
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==290;pins={}
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
assert records[-1]['target_name']=='AspisV8R19/TagBase' and records[-1]['base_revision']==base
lean=metrics(e/'lean/TagBase.log');s=(e/'lean/TagBase.log').read_text()
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s);assert len(axioms)==8
assert all(set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for x in axioms)
src=(root/'lean/AspisV8R19/TagBase.lean').read_text()
assert len(re.findall(r'^theorem ',src,re.M))==8 and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text())
def normalized(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x['instructions']for x in t['functions']}
before=normalized(oldtrace);after=normalized(trace)
deltas={n:before.get(n,0)-after.get(n,0)for n in before.keys()|after.keys()if before.get(n,0)!=after.get(n,0)}
assert sum(deltas.values())==oldtrace['executed_instructions']-trace['executed_instructions']==baseline[0]-cu[0]
receipt={'base_revision':base,'source_pins':195,'cu':cu,'baseline_cu':baseline,'saved_cu':[a-b for a,b in zip(baseline,cu)],
    'selected':all(b<a for a,b in zip(baseline,cu)),'actual_1M_gate_passed':False,'logs':logs,'trace':trace_time,
    'executed_instructions':trace['executed_instructions'],'executed_instruction_reduction':oldtrace['executed_instructions']-trace['executed_instructions'],
    'exclusive_function_instruction_reductions':deltas,'Lean':lean,'axioms_audits':8,'new_theorems':8,'final_cache_objects':290,
    'resources':{'RustHigh':'5G','RustMax':'7G','LeanHigh':'3G','LeanMax':'5G','runtimeHigh':'2G','runtimeMax':'3G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['r58_tag_base.rs','stage_r58_tag.py','run_r58_full.py','run_r58_lean.py','collect_r58_evidence.py','check_r58_evidence.py',
    'run_r23_full.py','run_r50_lean.py','build_r20_sbf.py','check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
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

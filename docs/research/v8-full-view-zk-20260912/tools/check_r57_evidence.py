#!/usr/bin/env python3
"""Source-delta, arithmetic-leaf and full-execution evidence gate for R57."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r57-selector-gather';parent=root/'evidence/r56-partial-product'
base='80aa7d98ebbc708ef54b947bb1810b913ddd21ec'
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
assert len(m['files'])==193 and len(pm['files'])==188
meta=m['r57_selector'];assert meta['base_revision']==base
assert meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
assert meta['source_registry_unchanged'] and meta['source_derived_const_table'] and not meta['protocol_changed']
ex='docs/research/v8-no-work-100-20260907/experiments/';mod='crates/aspis-statement/src/pool_v1/'
changed={n for n,h in m['files'].items()if pm['files'].get(n)!=h}
assert changed=={mod+'pair_forest_copy_terminal.rs',mod+'pair_forest_copy_terminal_constants.rs',
    mod+'r57_selector_gather.rs',ex+'performance-host/Cargo.toml',ex+'r57_selector_check.rs',ex+'r57_reference_copy.rs'}
for n in changed:assert sha(e/'source'/n)==m['files'][n]
assert sha(e/'source'/(ex+'r57_reference_copy.rs'))=='50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5'
assert m['files'][mod+'pair_forest_copy_terminal_constants.rs']=='cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50'
assert sha(root/'tools/r57_selector_gather.rs')==m['files'][mod+'r57_selector_gather.rs']
s=(e/'source'/(ex+'r57_reference_copy.rs')).read_text();old=function(s,'pub(crate) fn evaluate_with_selectors(')
start=old.index('    let mut link_index = 0usize;');loop=function(old[start:],'while link_index <');end=old.index(loop)+len(loop)
condition='all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")'
new=old[:start]+f'    #[cfg(not({condition}))]\n    {{\n'+old[start:end]+'\n    }\n'+f'    #[cfg({condition})]\n    r57_gather(&mut selector_tensor_scratch, selectors, append_index, variant);'+old[end:]
generated=s.replace(old,new)+'\n#[cfg(not(v8_performance_sbf))]\n'+old.replace('fn evaluate_with_selectors(','fn r57_reference_evaluate(')+'\n'+f'#[cfg({condition})]\ninclude!("r57_selector_gather.rs");\n'
assert (e/'source'/(mod+'pair_forest_copy_terminal.rs')).read_text()==generated
assert len(json.loads((e/'preflight/r18-stage.json').read_text())['files'])==191
logs={}
for kind,names in [('host',['selector-compile','selector-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    d=e/f'r24-{kind}-a';env=json.loads((d/'environment.json').read_text())
    assert env['source_manifest_sha256']==sha(e/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for n in names:logs[f'{kind}/{n}']=metrics(d/(n+'.log'))
control=(e/'r24-host-a/selector-check.log').read_text()
for x in ['source_terms=544','weight_checks=70720','scratch_and_full_lane_cases=512','both_variants=true','arbitrary_high_low=true','original_source=true']:assert x in control
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
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==289;pins={}
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
assert records[-1]['target_name']=='AspisV8R19/SelectorGather' and records[-1]['base_revision']==base
lean=metrics(e/'lean/SelectorGather.log');s=(e/'lean/SelectorGather.log').read_text()
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s);assert len(axioms)==6
assert all(set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for x in axioms)
src=(root/'lean/AspisV8R19/SelectorGather.lean').read_text()
assert len(re.findall(r'^theorem ',src,re.M))==6 and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text())
def normalized(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x['instructions']for x in t['functions']}
before=normalized(oldtrace);after=normalized(trace)
deltas={n:before.get(n,0)-after.get(n,0)for n in before.keys()|after.keys()if before.get(n,0)!=after.get(n,0)}
prefix='aspis_statement::pool_v1::pair_forest_copy_terminal::'
assert deltas=={prefix+'accumulate_endpoint_selector_tensor_basis':42549,
    prefix+'selected_binary_weight':2322,prefix+'evaluate_with_selectors':4387,prefix+'r57_gather':-17610}
receipt={'base_revision':base,'source_pins':193,'cu':cu,'baseline_cu':baseline,'saved_cu':[a-b for a,b in zip(baseline,cu)],
    'selected':all(b<a for a,b in zip(baseline,cu)),'actual_1M_gate_passed':False,'logs':logs,'trace':trace_time,
    'executed_instructions':trace['executed_instructions'],'executed_instruction_reduction':oldtrace['executed_instructions']-trace['executed_instructions'],
    'exclusive_function_instruction_reductions':deltas,
    'Lean':lean,'axioms_audits':6,'new_theorems':6,'final_cache_objects':289,
    'resources':{'RustHigh':'5G','RustMax':'7G','LeanHigh':'3G','LeanMax':'5G','runtimeHigh':'2G','runtimeMax':'3G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['r57_selector_gather.rs','stage_r57_selector.py','run_r57_full.py','run_r57_lean.py',
    'collect_r57_evidence.py','check_r57_evidence.py','run_r23_full.py','run_r50_lean.py','build_r20_sbf.py',
    'check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
for path in [root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',parent/'full-trace/analysis.json']:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text());assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),**{k:receipt[k]for k in ['cu','saved_cu','selected','new_theorems','actual_1M_gate_passed','full_privacy']}},indent=2))

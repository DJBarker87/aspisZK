#!/usr/bin/env python3
"""Check exact source deltas, retained regressions, formal leaf and complete CU."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r55-opening-decode';parent=root/'evidence/r27-sparse-preparation/shared'
base='85f18af7ce9078b751ca1b8fb981f1ce35396499'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(path):
    s=path.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,path
    assert not re.search(r'^error(?:\[|:)',s,re.M) and 'sorryAx' not in s,path
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
            'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
pm=json.loads((parent/'r18-stage.json').read_text());assert len(pm['files'])==182
assert sha(parent/'r18-stage.json')=='3c0741beddf4bc794a0e21fccc38fcfda7fd9aa227b0b2a3104d8121bd147f79'
ex='docs/research/v8-no-work-100-20260907/experiments/'
query=ex+'query_arithmetic.rs';cargo=ex+'performance-host/Cargo.toml';checker=ex+'r55_opening_check.rs'
original=(e/'control/query_arithmetic.rs').read_text();assert sha(e/'control/query_arithmetic.rs')==pm['files'][query]
old=function(original,'pub(super) fn combine_beta(')
start=old.index('    #[cfg(v8_decode_profile)]');end=old.index('    let mut out=')
new=old[:start]+'''    let mut c1_values=[0u32;104];
    r55_decode_into(c1,&mut c1_values)?;
    let mut c2_values=[0u32;48];
    r55_decode_into(c2,&mut c2_values)?;
    let c1=&c1_values;let c2=&c2_values;
'''+old[end:]
control_svm=json.loads((parent/'r24-svm-a/receipt.json').read_text())
results={};pins={}
for label,expected in [('buffer',[1621490,1622965]),('marker',[1612162,1613637])]:
    d=e/label;m=json.loads((d/'r18-stage.json').read_text());meta=m['r55_opening']
    assert len(m['files'])==183 and meta['base_revision']==base
    assert meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
    assert meta['branchless_canonicality']==(label=='marker') and meta['caller_owned_decode']
    assert not meta['protocol_changed'] and not meta['validation_removed']
    changed={n for n,h in m['files'].items()if pm['files'].get(n)!=h}
    assert changed=={query,cargo,checker} and set(m['files'])-set(pm['files'])=={checker}
    for n in changed:assert sha(d/'source'/n)==m['files'][n]
    helper=(root/'tools/r55_decode_into.rs').read_text()
    if label=='marker':
        helper=helper.replace('invalid|=u32::from(value==corelib::field::P);',
            '// value<=P, so value+1<=2^31: bit 31 marks exactly P.\n            invalid|=value+1;').replace('if invalid!=0','if invalid>>31!=0')
    generated=original.replace(old,new)+'\n'+helper+'\n#[cfg(not(v8_performance_sbf))]\n'+old.replace(
        'fn combine_beta(','fn r55_reference_combine_beta(')+'\n'+(root/'tools/r55_opening_controls.rs').read_text()
    assert (d/'source'/query).read_text()==generated
    ms=sha(d/'r18-stage.json')
    logs={}
    for kind,names in [('host',['opening-compile','opening-check','compile','wire-controls','world0','world1']),
                       ('sbf',['compile']),('svm',['world0','world1'])]:
        folder=d/f'r24-{kind}-a';env=json.loads((folder/'environment.json').read_text())
        assert env['source_manifest_sha256']==ms and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
        for n in names:logs[f'{kind}/{n}']=metrics(folder/(n+'.log'))
    opening=(d/'r24-host-a/opening-check.log').read_text()
    for marker in ['canonical_comparisons=2048','malformed_and_order=2232','poisoned_output_cases=1024',
                   'beta_zero_one_retained=true','all_152_limbs_checked=true','source_reference=true']:assert marker in opening
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (d/f'r24-host-a/world{w}.log').read_text()
    wire=json.loads((d/'r24-host-a/wire-controls/results.json').read_text())
    assert len(wire['cases'])==3281 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection'] for x in wire['cases'])==3280
    sbf=(d/'r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in sbf and not ('Stack offset' in sbf and 'exceeded' in sbf)
    svm=json.loads((d/'r24-svm-a/receipt.json').read_text());assert svm['source_manifest_sha256']==ms
    assert svm['elf_sha256']==json.loads((d/'r24-sbf-a/environment.json').read_text())['elf_sha256']
    assert svm['full_verifier'] and not svm['instrumented']
    assert len(svm['runs'])==2 and svm['driver_sha256']==control_svm['driver_sha256']
    for w,r in enumerate(svm['runs']):
        assert r['world']==w and r['proof_sha256']==control_svm['runs'][w]['proof_sha256']
        rows=r['results'];assert len(rows)==4
        assert all(x['heap_bytes']==262144 and x['unchanged_accounts'] for x in rows)
        for x in rows:
            if x['cu_limit']==1000000:
                assert x['resource_failure'] and not x['accepted'] and not x['custom_rejection'] and x['cu']==1000000
            else:
                assert x['cu_limit']==100000000 and not x['resource_failure']
                if x['case']=='honest':assert x['accepted'] and x['cu']==expected[w]
                else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted']
    assert svm['runs'][0]['proof_sha256']!=svm['runs'][1]['proof_sha256']
    results[label]={'cu':expected,'selected':label=='marker','logs':logs,'elf_sha256':svm['elf_sha256']}
records=json.loads((e/'lean-b/metadata.json').read_text());assert len(records)==287
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256']
    pins[str(path.relative_to(repo))]=sha(path)
leaf=records[-1];assert leaf['target_name']=='AspisV8R19/PackedCanonicalMarker' and leaf['base_revision']==base
lean=metrics(e/'lean-b/PackedCanonicalMarker.log')
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',(e/'lean-b/PackedCanonicalMarker.log').read_text())
assert len(axioms)==5 and all(set(x.replace(' ','').split(','))=={'propext','Quot.sound'}for x in axioms)
assert '\tExit status: 1' in (e/'lean-a/PackedCanonicalMarker.log').read_text()
source=(root/'lean/AspisV8R19/PackedCanonicalMarker.lean').read_text()
assert len(re.findall(r'^theorem ',source,re.M))==5 and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',source)
trace=json.loads((e/'marker/full-trace/analysis.json').read_text())
tr=json.loads((e/'marker/full-trace/receipt.json').read_text())
assert trace['exact_text_match'] and tr['clean_cu_equal'] and trace['cu']==tr['result']['cu']==1612162
assert trace['elf_sha256']==tr['elf_sha256']==results['marker']['elf_sha256']
assert trace['executed_instructions']==1507099
trace_metrics=metrics(e/'marker/full-trace/run.log')
baseline_trace=json.loads((parent/'full-trace/analysis.json').read_text())
def counts(t,part):return sum(x['instructions']for x in t['functions']if part in x['name'])
assert counts(trace,'field::QM31::mul::')==counts(baseline_trace,'field::QM31::mul::')==327881
receipt={'base_revision':base,'selected':'marker','experiments':results,'Lean':lean,'new_theorems':5,
    'axioms_audits':5,'allowed_axioms':['propext','Quot.sound'],'final_cache_objects':287,
    'canonical_comparisons_per_candidate':2048,'malformed_order_controls_per_candidate':2232,
    'wire_controls_per_candidate':3281,'source_pins_per_candidate':183,
    'baseline_cu':[1620236,1621719],'saved_cu':[8074,8082],'actual_1M_gate_passed':False,
    'trace':trace_metrics,'executed_instruction_reduction':baseline_trace['executed_instructions']-trace['executed_instructions'],
    'resource_policy_record':{'LeanHigh':'3G','LeanMax':'5G','RustHigh':'5G','RustMax':'7G',
        'traceHigh':'2G','traceMax':'3G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'protocol_changed':False,'new_hiding_assumptions':False,'universal_Rust_refinement':False,
    'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['collect_r55_evidence.py','check_r55_evidence.py','stage_r55_opening.py','r55_decode_into.rs',
    'r55_opening_controls.rs','run_r55_full.py','run_r23_full.py','build_r20_sbf.py','check_r19_wire_controls.py',
    'run_r55_lean.py','run_r50_lean.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
for path in [root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',
    parent/'full-trace/analysis.json',root/'evidence/r54-sampler-wrappers/MANIFEST.json']:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt
assert json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),
    'cu':results['marker']['cu'],'new_theorems':5,'actual_1M_gate_passed':False,'full_privacy':False},indent=2))

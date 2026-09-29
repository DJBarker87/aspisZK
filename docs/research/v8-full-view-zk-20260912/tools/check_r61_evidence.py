#!/usr/bin/env python3
"""Audit retained-kernel reuse, exact source delta and complete SBF evidence."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r61-opening';parent=root/'evidence/r59-partial-dot'
base='61b0a3ce324647396a9bf7e911222391e8126958'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^error(?:\[|:)',s,re.M),p
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
def function(s,needle):
    start=s.index(needle);b=s.index('{',start);depth=0
    for i in range(b,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
m=json.loads((e/'r18-stage.json').read_text());pm=json.loads((parent/'r18-stage.json').read_text())
assert len(m['files'])==197 and len(pm['files'])==195
meta=m['r61_opening'];assert meta['base_revision']==base and meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
assert meta['retained_fixed_dot'] and not any(meta[k]for k in ['protocol_changed','validation_removed','production_changed'])
ex='docs/research/v8-no-work-100-20260907/experiments/'
changes={'r17-stage.json','r17-sbf-probe.json',ex+'query_arithmetic.rs',ex+'r55_opening_check.rs'}
assert {n for n,h in m['files'].items()if pm['files'].get(n)!=h}==changes
assert set(pm['files'])<=set(m['files'])
for n in changes:
    assert sha(e/'source'/n)==m['files'][n]
    if n in pm['files']:assert sha(e/'control'/n)==pm['files'][n]
for n in ['r17-stage.json','r17-sbf-probe.json']:
    old=json.loads((e/'control'/n).read_text());new=json.loads((e/'source'/n).read_text())
    assert 'v8_gamma_fixed' not in old['rustflags'] and 'v8_gamma_fused' not in old['rustflags']
    old['rustflags']+=' --cfg v8_gamma_fixed';assert old==new
    assert '--cfg v8_gamma_partial' in new['rustflags']
old=(e/'control'/ex/'query_arithmetic.rs').read_text();new=(e/'source'/ex/'query_arithmetic.rs').read_text()
assert new==old+'\n'+(root/'tools/r61_opening_controls.rs').read_text()
check=(e/'control'/ex/'r55_opening_check.rs').read_text()
assert (e/'source'/ex/'r55_opening_check.rs').read_text()==check.replace('query_arithmetic::r55_controls();','query_arithmetic::r55_controls();query_arithmetic::r61_controls();')
retained=repo/ex/'query_arithmetic.rs'
assert function(old,'fn fixed_dot<')==function(retained.read_text(),'fn fixed_dot<')
assert 'sum.map(M31::reduce_u64)' in old and 'if invalid>>31!=0' in old
logs={}
for kind,names in [('host',['opening-compile','opening-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
    d=e/f'r24-{kind}-a';env=json.loads((d/'environment.json').read_text())
    assert env['source_manifest_sha256']==sha(e/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    for n in names:logs[f'{kind}/{n}']=metrics(d/(n+'.log'))
checks=(e/'r24-host-a/opening-check.log').read_text()
for marker in ['canonical_comparisons=2048','malformed_and_order=2232','all_152_limbs_checked=true',
    'canonical_profiles=512 maximal_limb_dot=true noncanonical_positions=152 short_inputs=2',
    'scalar_u128_comparisons=16384 packed_arbitrary_matrices=4096 canonical_max=true all_basis_positions=true']:assert marker in checks
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
            else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted'] and x['error']=='InstructionError(0, Custom(6))'
assert svm['runs'][0]['proof_sha256']!=svm['runs'][1]['proof_sha256']
assert cu==[1507423,1508805] and baseline==[1516838,1518195]
trace=json.loads((e/'full-trace/analysis.json').read_text());tr=json.loads((e/'full-trace/receipt.json').read_text())
assert trace['elf_sha256']==tr['elf_sha256']==svm['elf_sha256']
assert trace['exact_text_match'] and tr['clean_cu_equal'] and trace['cu']==tr['result']['cu']==cu[0]
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text())
def normalized(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x['instructions']for x in t['functions']}
before=normalized(oldtrace);after=normalized(trace)
deltas={n:before.get(n,0)-after.get(n,0)for n in before.keys()|after.keys()if before.get(n,0)!=after.get(n,0)}
assert sum(deltas.values())==oldtrace['executed_instructions']-trace['executed_instructions']==baseline[0]-cu[0]
assert deltas=={'aspis_v8_performance_sbf::query_arithmetic::combine_beta':9415}
lean=repo/ex/'GammaDotUnroll.lean';prooflog=repo/ex/'gamma-fixed-final-lean.log'
s=prooflog.read_text();assert sha(lean) in s and 'sorryAx' not in s and 'error:' not in s
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s);assert len(axioms)==4
assert all(set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for x in axioms)
receipt={'base_revision':base,'source_pins':197,'cu':cu,'baseline_cu':baseline,'saved_cu':[x-y for x,y in zip(baseline,cu)],
    'selected':True,'actual_1M_gate_passed':False,'logs':logs,'trace':metrics(e/'full-trace/run.log'),
    'executed_instructions':trace['executed_instructions'],'exclusive_function_instruction_reductions':deltas,
    'new_theorems':0,'retained_Lean_axioms_audits':4,'retained_Lean_source_sha256':sha(lean),
    'resources':{'RustHigh':'5G','RustMax':'7G','runtimeHigh':'2G','runtimeMax':'3G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':7},
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['stage_r61_opening.py','r61_opening_controls.rs','run_r61_full.py','collect_r61_evidence.py','check_r61_evidence.py',
    'run_r23_full.py','build_r20_sbf.py','check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
paths=[root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',parent/'full-trace/analysis.json',lean,prooflog,retained,
    repo/ex/'M31RangeKernels.lean',repo/ex/'QmCrossRange.lean']
pins={str(f.relative_to(repo)):sha(f)for f in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');(e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text());assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),**{k:receipt[k]for k in ['cu','saved_cu','selected','new_theorems','actual_1M_gate_passed','full_privacy']}},indent=2))

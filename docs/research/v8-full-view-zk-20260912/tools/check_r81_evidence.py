#!/usr/bin/env python3
"""Audit complete native-CU evidence; no claim of global privacy or soundness."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r81-native'
ex='docs/research/v8-no-work-100-20260907/experiments/'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def readj(f):return json.loads(f.read_text())
def metrics(f):
    s=f.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,f
    assert not re.search(r'^error(?:\[|:)',s,re.M),f
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[1].split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
pm=readj(e/'control/r18-stage.json');control=readj(e/'control/svm.json')
assert len(pm['files'])==202
assert sha(e/'control/r18-stage.json')=='6a8d46585bcebaeca27fbb88c936e2379ce45f3f314a01f7d37d7b995bb8e8ab'
oldsrc=readj(e/'control/sources.json')
for n,h in oldsrc.items():assert h==pm['files'][n];blob(h)
expected={'square':[1468197,1469590],'shortdot':[1439254,1440522],
    'semantic':[1425186,1426443],'powerbasis':[1417341,1418557],
    'shortinline':[1406069,1407329],'compose':[1398224,1399443],
    'privatebasis':[1385494,1386734],'scalarg':[1356211,1357487]}
reports={}
for variant,wanted in expected.items():
    d=e/variant;m=readj(d/'r18-stage.json');sources=readj(d/'sources.json');arts=readj(d/'artifacts.json')
    def artifact(n):return blob(arts[n])
    def source(n):return blob(sources[n]).read_text()
    assert m['r81_native']['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert m['r81_native']['base_revision']=='4b64f97254e18f0338e1ad6229ca8407143aeb2b'
    assert m['r81_native']['variant']==('square-shortdot'if variant=='shortdot'else variant)
    assert not m['r81_native']['protocol_changed'] and not m['r81_native']['validation_removed']
    assert set(pm['files'])<=set(m['files'])
    assert sources=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for n,h in sources.items():assert blob(h).is_file()
    changed={n for n in sources if n in pm['files']}
    allowed={'crates/aspis-core/src/field.rs',ex+'performance-host/Cargo.toml'}
    if variant not in ['square','shortdot']:allowed.add(ex+'performance_verifier.rs')
    has_basis=variant in ['powerbasis','compose','privatebasis','scalarg']
    if has_basis:allowed.add(ex+'r20_semantic_basis.rs')
    if variant=='scalarg':allowed|={ex+n for n in ['r22_scalar.rs','r17_host_relation.rs','r27_native.rs','r27_check.rs']}
    assert changed==allowed,(variant,changed^allowed)
    new={ex+'r81_reference/'+n for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']}
    new.add(ex+'r81_square_check.rs')
    if has_basis:new|={ex+'r81_reference/r20_semantic_basis.rs',ex+'r81_basis_check.rs'}
    if variant in ['privatebasis','scalarg']:new.add(ex+'r81_canonical_basis.rs')
    assert set(m['files'])-set(pm['files'])==new
    for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
        assert m['files'][ex+'r81_reference/'+n]==pm['files']['crates/aspis-core/src/'+n]
    if has_basis:assert m['files'][ex+'r81_reference/r20_semantic_basis.rs']==pm['files'][ex+'r20_semantic_basis.rs']
    # The original guarded product, full reducer and fallback sources stay
    # pinned. No parser/authentication/transcript/basis-map source is changed.
    field=source('crates/aspis-core/src/field.rs')
    assert 'if let Some(result)=r24_canonical_mul(self,self) {return result;}' in field
    if variant!='square':
        helper=(root/'tools/r81_short_dot.rs').read_text()
        if variant in ['shortinline','compose','privatebasis','scalarg']:
            helper=helper.replace('#[inline(never)]\nfn r81_short_dot','#[inline(always)]\nfn r81_short_dot')
        assert field.endswith('\n'+helper)
    if variant in ['privatebasis','scalarg']:
        q=source(ex+'r81_canonical_basis.rs')
        assert 'pub struct Q([u32;4]);' in q and 'pub fn from_limbs' in q
        assert 'from_reduced_limbs' not in q and 'unsafe' not in q
    if variant=='scalarg':
        assert source(ex+'r22_scalar.rs')==blob(oldsrc[ex+'r22_scalar.rs']).read_text()+'\n'+(root/'tools/r81_sparse_scalar.rs').read_text()
        v=source(ex+'r17_host_relation.rs')
        assert v.index('::terminal_scalar(')<v.index('::r81_sparse_scalar_after_ordinary(')
        for needle in ['if terminal!=claim{return Err(Error::Terminal)}','let image_scale=K::ONE.sub(beta).add(beta.mul(p.tau.square()));',
            'let (values,xs)=opened_channel(w,&p,iv_g,&queries,a,beta)?;']:
            assert needle in v and needle in blob(oldsrc[ex+'r17_host_relation.rs']).read_text()
    logs={};resources={}
    for name,h in arts.items():
        f=blob(h)
        if name.endswith('.log'):logs[name]=metrics(f)
        if name.endswith('/resources.json'):
            r=readj(f);mode=name.split('-')[1];hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[mode]
            assert {k:r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
                'memory.high':str(hi*2**30),'memory.max':str(ma*2**30),'memory.swap.max':'0','pids.max':'128'}
            resources[mode]=r
    for mode in ['host','sbf','svm']:
        env=readj(artifact(f'r24-{mode}-a/environment.json'))
        assert env['source_manifest_sha256']==sha(d/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    square=artifact('r24-host-a/square-check.log').read_text()
    assert 'canonical=265536 boundary=65536 random=200000 invalid=60' in square
    if variant!='square':assert 'short_dot_comparisons=49152' in square
    if has_basis:
        basis=artifact('r24-host-a/basis-check.log').read_text()
        assert 'vectors=8192 scaling_comparisons=90112 semantic_rounds=2560 raw_basis=12 raw_scaling=132' in basis
    if variant in ['privatebasis','scalarg']:assert 'R81_PRIVATE' in basis and '796608' in basis
    if variant=='scalarg':assert 'R81_SCALAR_G arbitrary=256 selected_basis=271 cache_postconditions=256' in artifact('r24-host-a/ordinary-check.log').read_text()
    wire=readj(artifact('wire-controls.json'))
    assert len(wire['cases'])==3281 and sum(x['checked_rejection']for x in wire['cases'])==3280
    assert all(x['exit']==0 for x in wire['cases'])
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in artifact(f'r24-host-a/world{w}.log').read_text()
    build=artifact('r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
    svm=readj(artifact('r24-svm-a/receipt.json'))
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['elf_sha256']==readj(artifact('r24-sbf-a/environment.json'))['elf_sha256']
    assert svm['driver_sha256']==control['driver_sha256'] and svm['full_verifier'] and not svm['instrumented']
    cu=[];assert len(svm['runs'])==2
    for w,run in enumerate(svm['runs']):
        assert run['world']==w and run['proof_sha256']==control['runs'][w]['proof_sha256'] and len(run['results'])==4
        for r in run['results']:
            assert r['heap_bytes']==262144 and r['unchanged_accounts']
            if r['cu_limit']==1000000 and r['case']=='honest':
                assert r['cu']==1000000 and r['resource_failure'] and not r['accepted'] and not r['custom_rejection']
            elif r['cu_limit']==1000000:
                assert r['case']=='bad-combined-final' and not r['accepted']
                if r['resource_failure']:assert r['cu']==1000000 and not r['custom_rejection']
                else:assert r['custom_rejection'] and r['cu']<=1000000 and r['error']=='InstructionError(0, Custom(6))'
            else:
                assert r['cu_limit']==100000000 and not r['resource_failure']
                if r['case']=='honest':assert r['accepted'];cu.append(r['cu'])
                else:assert r['case']=='bad-combined-final' and r['custom_rejection'] and not r['accepted'] and r['error']=='InstructionError(0, Custom(6))'
    assert cu==wanted
    if 'full-trace/analysis.json' in arts:
        t=readj(artifact('full-trace/analysis.json'));r=readj(artifact('full-trace/receipt.json'))
        assert t['exact_text_match'] and t['elf_sha256']==r['elf_sha256']==svm['elf_sha256']
        assert t['cu']==r['result']['cu']==cu[0] and r['clean_cu_equal']
    reports[variant]={'cu':cu,'source_pins':len(m['files']),'elf_sha256':svm['elf_sha256'],
        'metrics':logs,'captured_cgroup_properties':resources,'selected_endpoint':variant=='scalarg'}
receipt={'base_revision':'4b64f97254e18f0338e1ad6229ca8407143aeb2b','control_cu':[1495663,1497050],
    'variants':reports,'selected_cu':[1356211,1357487],'remaining_worst_case_cu':357487,
    'actual_1M_gate_passed':False,'protocol_changed':False,'validation_removed':False,
    'new_Lean_theorems':0,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,
    'requested_caps_gib':{'host':[5,7],'sbf':[12,16],'svm':[2,3],'analysis':[1,2]},
    'MemorySwapMax':0,'max_simultaneous_reservation_gib':26,
    'early_cgroup_capture_missing':'All jobs launched with explicit caps; old runner did not persist properties. Never synthesized retrospectively.'}
paths=[root/'tools'/n for n in ['stage_r81_native.py','run_r81_full.py','r81_square_check.rs','r81_short_dot.rs',
    'r81_basis_check.rs','r81_scale.rs','r81_private_check.rs','r81_sparse_scalar.rs','r81_mul_inventory.py',
    'collect_r81_evidence.py','check_r81_evidence.py','run_r69_full.py','run_r23_full.py','build_r20_sbf.py',
    'check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']]
pins={str(f.relative_to(repo)):sha(f)for f in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert readj(e/'receipt.json')==receipt and readj(e/'SOURCE_PINS.json')==pins
manifest=readj(e/'MANIFEST.json')
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'selected_cu':receipt['selected_cu'],
    'remaining_worst_case_cu':357487,'actual_1M_gate_passed':False,'full_privacy':False},indent=2))

#!/usr/bin/env python3
"""Audit measured follow-ups, including correct-but-slower rejected variants."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r82-native';parent=root/'evidence/r81-native'
subprocess.run([sys.executable,str(root/'tools/check_r81_evidence.py')],check=True,stdout=subprocess.DEVNULL)
ex='docs/research/v8-no-work-100-20260907/experiments/'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s
    assert not re.search(r'^error(?:\[|:)',s,re.M)
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[1].split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
pm=j(e/'control/r18-stage.json');control=j(e/'control/svm.json')
assert sha(e/'control/r18-stage.json')==sha(parent/'scalarg/r18-stage.json')=='befe62a23b9ad254a82ac068ee277790e48c172a12acb324fc0555ab075c6263'
parent_arts=j(parent/'scalarg/artifacts.json')
assert sha(e/'control/svm.json')==parent_arts['r24-svm-a/receipt.json']
original=j(e/'control/sources.json')
for n,h in original.items():assert h==pm['files'][n];blob(h)
reports={}
expected={'pair':[1346806,1348070],'inline':[1356726,1358040],
    'affine':[1354455,1355729],'compose':[1336800,1337989],
    'unroll':[1350300,1351489],'dotinline':[1333812,1335001],
    'matrix':[1335293,1336491]}
for variant in ['pair','inline','affine','compose','unroll','dotinline','matrix']:
    d=e/variant;m=j(d/'r18-stage.json');sources=j(d/'sources.json');arts=j(d/'artifacts.json')
    def artifact(n):return blob(arts[n])
    assert m['r82_native']['variant']==variant and m['r82_native']['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not m['r82_native']['protocol_changed'] and not m['r82_native']['validation_removed']
    assert set(m['files'])==set(pm['files']) and len(m['files'])==210
    assert sources=={n:h for n,h in m['files'].items()if pm['files'][n]!=h}
    for n,h in sources.items():blob(h)
    allowed=set()
    if variant in ['pair','compose','unroll','dotinline','matrix']:
        allowed|={ex+n for n in ['r19_channel_ordinary.rs','r22_scalar.rs','r27_native.rs','r27_check.rs']}
    if variant in ['affine','compose','unroll','dotinline','matrix']:allowed.add(ex+'query_arithmetic.rs')
    if variant in ['inline','matrix']:allowed.add('crates/aspis-core/src/field.rs')
    if variant=='dotinline':allowed.add('crates/aspis-core/src/r25_checked_dot.rs')
    if variant=='unroll':allowed.add(ex+'r20_semantic_basis.rs')
    assert set(sources)==allowed
    if variant=='dotinline':
        n='crates/aspis-core/src/r25_checked_dot.rs'
        assert blob(sources[n]).read_text()==blob(original[n]).read_text().replace('#[inline(never)]\npub fn r25_checked_dot','#[inline(always)]\npub fn r25_checked_dot')
    logs={};resources={}
    for n,h in arts.items():
        f=blob(h)
        if n.endswith('.log'):logs[n]=metrics(f)
        if n.endswith('/resources.json'):
            r=j(f);mode=n.split('-')[1];hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[mode]
            assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
            resources[mode]=r
    assert set(resources)=={'host','sbf','svm'}
    for mode in resources:
        env=j(artifact(f'r24-{mode}-a/environment.json'))
        assert env['source_manifest_sha256']==sha(d/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    assert 'canonical=265536' in artifact('r24-host-a/square-check.log').read_text()
    assert 'short_dot_comparisons=49152' in artifact('r24-host-a/square-check.log').read_text()
    assert 'R81_SCALAR_G arbitrary=256 selected_basis=271 cache_postconditions=256' in artifact('r24-host-a/ordinary-check.log').read_text()
    if variant in ['pair','compose','unroll','dotinline','matrix']:
        assert 'R82_PAIR entry_comparisons=262144' in artifact('r24-host-a/ordinary-check.log').read_text()
    wire=j(artifact('wire-controls.json'))
    assert len(wire['cases'])==3281 and sum(r['checked_rejection']for r in wire['cases'])==3280
    assert all(r['exit']==0 for r in wire['cases'])
    build=artifact('r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in build and not('Stack offset' in build and 'exceeded' in build)
    svm=j(artifact('r24-svm-a/receipt.json'))
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['elf_sha256']==j(artifact('r24-sbf-a/environment.json'))['elf_sha256']
    assert svm['driver_sha256']==control['driver_sha256'] and svm['full_verifier'] and not svm['instrumented']
    cu=[]
    for w,r in enumerate(svm['runs']):
        assert r['world']==w and r['proof_sha256']==control['runs'][w]['proof_sha256']
        assert len(r['results'])==4
        for x in r['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000 and x['case']=='honest':
                assert x['cu']==1000000 and x['resource_failure'] and not x['accepted'] and not x['custom_rejection']
            elif x['cu_limit']==1000000:
                assert x['case']=='bad-combined-final' and not x['accepted']
                if x['resource_failure']:assert x['cu']==1000000 and not x['custom_rejection']
                else:assert x['custom_rejection'] and x['error']=='InstructionError(0, Custom(6))'
            else:
                assert x['cu_limit']==100000000 and not x['resource_failure']
                if x['case']=='honest':assert x['accepted'];cu.append(x['cu'])
                else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted'] and x['error']=='InstructionError(0, Custom(6))'
    if variant in expected:assert cu==expected[variant]
    assert len(cu)==2
    if 'full-trace/analysis.json' in arts:
        t=j(artifact('full-trace/analysis.json'));r=j(artifact('full-trace/receipt.json'))
        assert t['elf_sha256']==r['elf_sha256']==svm['elf_sha256'] and t['exact_text_match']
        assert t['cu']==r['result']['cu']==cu[0] and r['clean_cu_equal']
    reports[variant]={'cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs,'resources':resources}
selected=min(reports,key=lambda n:max(reports[n]['cu']))
receipt={'control_cu':[1356211,1357487],'variants':reports,'selected':selected,'selected_cu':reports[selected]['cu'],
    'remaining_worst_case_cu':max(reports[selected]['cu'])-1000000,'actual_1M_gate_passed':False,
    'new_Lean_theorems':0,'protocol_changed':False,'validation_removed':False,
    'full_privacy':False,'full_soundness':False,'universal_Rust_refinement':False}
paths=[root/'tools'/n for n in ['stage_r82_native.py','collect_r82_evidence.py','check_r82_evidence.py','collect_r81_evidence.py','run_r81_full.py','r62_entry.rs']]+[parent/'MANIFEST.json']
pins={str(f.relative_to(repo)):sha(f)for f in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h
print(json.dumps({'status':'PASS','selected':selected,'cu':reports[selected]['cu'],'artifacts':len(manifest),
    'actual_1M_gate_passed':False},indent=2))

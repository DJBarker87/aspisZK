#!/usr/bin/env python3
"""Audit exact-output R83 results; preserve compiler/frame failures as failures."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r83-native';parent=root/'evidence/r82-native'
subprocess.run([sys.executable,str(root/'tools/check_r82_evidence.py')],check=True,stdout=subprocess.DEVNULL)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)
    if not t:return {'timing_missing':True}
    return {'exit':int(re.search(r'Exit status: (\d+)',s)[1]),'swaps':int(re.search(r'Swaps: (\d+)',s)[1]),
        'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t[1].split(':')))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
pm=j(e/'control/r18-stage.json');control=j(e/'control/svm.json')
assert sha(e/'control/r18-stage.json')==sha(parent/'dotinline/r18-stage.json')=='f70d74f4e479899b7eda0664a4dfdf4b8e8068d7bf9be836a2cd681397167498'
assert sha(e/'control/svm.json')==j(parent/'dotinline/artifacts.json')['r24-svm-a/receipt.json']
original=j(e/'control/sources.json')
for n,h in original.items():
    if n in pm['files']:assert h==pm['files'][n]
    blob(h)
expected={'tensor':[1335325,1336521],'blockdot':[1331290,1332484],
    'packed':[1329509,1330704],'packed-block':[1326977,1328177]}
reports={};ex='docs/research/v8-no-work-100-20260907/experiments/'
for variant in [*expected,'packed-failed','opt2']:
    d=e/variant;m=j(d/'r18-stage.json');sources=j(d/'sources.json');arts=j(d/'artifacts.json')
    def art(n):return blob(arts[n])
    assert m['r83_native']['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not m['r83_native']['protocol_changed'] and not m['r83_native']['validation_removed']
    assert sources=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for n,h in sources.items():blob(h)
    # No frozen input file can disappear; only the previously unpinned SBF
    # profile may be newly added. Older completed stages retain their pins.
    extra=set(m['files'])-set(pm['files']);assert set(pm['files'])<=set(m['files'])
    assert extra<= {ex+'performance-sbf/Cargo.toml'}
    allowed={ex+'performance-sbf/Cargo.toml'}
    if variant in ['tensor','blockdot','packed-block']:allowed|={ex+'r19_channel_ordinary.rs',ex+'r27_check.rs'}
    if variant=='tensor':allowed.add(ex+'r27_native.rs')
    if variant in ['packed','packed-failed','packed-block']:allowed|={ex+'query_arithmetic.rs',ex+'r55_opening_check.rs'}
    assert set(sources)<=allowed
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    for r in logs.values():
        if 'swaps'in r:assert r['swaps']==0
    if variant in ['packed-failed','opt2']:
        assert not any(n.startswith('r24-svm-')for n in arts)
        build=art('r24-sbf-a/compile.log').read_text()
        if variant=='opt2':
            assert 'overflows the maximum allowed frame' in build
            assert '4288' in build and '4416' in build and '6208' in build
            assert j(art('host-reuse.json'))['host_replayed'] is False
        else:
            assert 'mismatched closing delimiter' in build
            assert 'mismatched closing delimiter' in art('r24-host-a/opening-compile.log').read_text()
        reports[variant]={'selected':False,'simulated':False,'logs':logs,
            'failure':'stack frame diagnostic'if variant=='opt2'else'Rust syntax',
            'limits_receipt_missing':variant=='opt2'}
        continue
    resources={}
    for mode in ['host','sbf','svm']:
        r=j(art(f'r24-{mode}-a/resources.json'));hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[mode]
        assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128'];resources[mode]=r
        env=j(art(f'r24-{mode}-a/environment.json'))
        assert env['source_manifest_sha256']==sha(d/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
    assert all(r.get('exit')==0 for r in logs.values())
    assert 'R81_SCALAR_G arbitrary=256 selected_basis=271 cache_postconditions=256' in art('r24-host-a/ordinary-check.log').read_text()
    if variant in ['packed','packed-block']:
        assert 'R83_PACKED arbitrary_coefficient_profiles=4096' in art('r24-host-a/opening-check.log').read_text()
        assert 'R61_' in art('r24-host-a/opening-check.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3281
    assert sum(x['checked_rejection']for x in wire['cases'])==3280 and all(x['exit']==0 for x in wire['cases'])
    build=art('r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in build and not('Stack offset' in build and 'exceeded' in build)
    svm=j(art('r24-svm-a/receipt.json'));assert svm['full_verifier'] and not svm['instrumented']
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['driver_sha256']==control['driver_sha256']
    assert svm['elf_sha256']==j(art('r24-sbf-a/environment.json'))['elf_sha256']
    cu=[]
    for w,r in enumerate(svm['runs']):
        assert r['world']==w and r['proof_sha256']==control['runs'][w]['proof_sha256']
        assert len(r['results'])==4
        for x in r['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['case']=='honest':
                if x['cu_limit']==1000000:assert x['cu']==1000000 and x['resource_failure'] and not x['accepted'] and not x['custom_rejection']
                else:assert x['cu_limit']==100000000 and x['accepted'] and not x['resource_failure'];cu.append(x['cu'])
            else:
                assert x['case']=='bad-combined-final' and not x['accepted']
                if x['resource_failure']:assert x['cu_limit']==x['cu']==1000000 and not x['custom_rejection']
                else:assert x['custom_rejection'] and x['error']=='InstructionError(0, Custom(6))'
    assert cu==expected[variant]
    reports[variant]={'cu':cu,'elf_sha256':svm['elf_sha256'],'logs':logs,'resources':resources}
receipt={'variants':reports,'selected':'packed-block','cu':expected['packed-block'],'saved_vs_R82':[6835,6824],
    'remaining_cu':328177,'actual_1M_pass':False,'protocol_changed':False,'validation_removed':False,
    'new_Lean_targets':0,'full_privacy':False,'full_soundness':False}
pins={str(f.relative_to(repo)):sha(f)for f in [root/'tools'/n for n in ['stage_r83_native.py','run_r83_full.py','r83_packed.rs','r83_block_dot.rs','r83_tensor.rs','collect_r83_evidence.py','check_r83_evidence.py']]+[parent/'MANIFEST.json']}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h
print(json.dumps({'status':'PASS','cu':expected['packed-block'],'artifacts':len(manifest),'actual_1M_pass':False}))

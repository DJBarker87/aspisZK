#!/usr/bin/env python3
"""Audit same-proof native kernels and scoped circle-observer correspondence."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r85-private-circle'
for n in ['check_r84_evidence.py','check_r80_evidence.py']:
    subprocess.run([sys.executable,str(root/'tools'/n)],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[1]
    return {'exit':int(re.search(r'Exit status: (\d+)',s)[1]),'swaps':int(re.search(r'Swaps: (\d+)',s)[1]),
        'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r84-bitperm/compact/r18-stage.json')
original=j(e/'control/sources.json')
for n,h in original.items():assert h==pm['files'][n];blob(h)
ex='docs/research/v8-no-work-100-20260907/experiments/'
reports={};expected={'quotient-b':[1202355,1200492],'ordinary-b':[1209805,1207999],'compose-a':[1199479,1197630]}
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
for variant in ['quotient-a','quotient-b','ordinary-a','ordinary-b','compose-a']:
    d=e/variant;m=j(d/'r18-stage.json');sources=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert set(m['files'])==set(pm['files']) and len(m['files'])==212
    assert sources=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    v=m['r85_native'];assert v['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not v['protocol_changed'] and not v['validation_removed'] and not v['new_security_claim']
    assert [f['sha256']for f in v['fixtures']]==proofs
    allowed={'r81_canonical_basis.rs'}
    if v['variant'] in ['quotient','compose']:allowed|={'quotient_fold.rs','r17_host_relation.rs','r55_opening_check.rs'}
    if v['variant'] in ['ordinary','compose']:allowed|={'r19_channel_ordinary.rs'};allowed|=set()if variant=='ordinary-a'else{'r84_bitperm_check.rs'}
    assert set(sources)=={ex+n for n in allowed},variant
    for h in sources.values():blob(h)
    q=blob(sources[ex+'r81_canonical_basis.rs']).read_text()
    assert q==blob(original[ex+'r81_canonical_basis.rs']).read_text()+'\n'+(root/'tools/r85_private_ops.rs').read_text()
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(v['swaps']==0 for v in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            r=j(blob(h));hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
    def art(n):return blob(arts[n])
    if variant not in expected:
        assert any(r['exit']==101 for r in logs.values())and 'r24-svm-a/receipt.json'not in arts
        reports[variant]={'status':'compile_failure_retained','metrics':logs};continue
    assert all(x['exit']==0 for x in logs.values())
    assert 'full_dual_chord_image_final_cases=64' in art('r24-host-a/compact-check.log').read_text()
    if v['variant']in ['quotient','compose']:
        assert 'arbitrary_full_kernel_comparisons=8192' in art('r24-host-a/opening-check.log').read_text()
        text=blob(sources[ex+'r17_host_relation.rs']).read_text()
        assert 'Decode every limb even when its coefficient is zero' in text
        assert 'verify_two_minimal_subtrees_v7_bytes('in text and '.try_inv().ok_or(Error::Domain)?'in text
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==3281
    build=art('r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame'not in build and not('Stack offset'in build and 'exceeded'in build)
    assert 'all 1024 source permutation and inactive entries match SBF table'in build
    svm=j(art('r24-svm-a/receipt.json'));assert svm['full_verifier']and not svm['new_profile']and not svm['security_promoted']
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['elf_sha256']==j(art('r24-sbf-a/environment.json'))['elf_sha256']
    assert [r['proof_sha256']for r in svm['runs']]==proofs
    cu=[]
    for r in svm['runs']:
        assert len(r['results'])==4
        for x in r['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['case']=='honest':
                if x['cu_limit']==100000000:assert x['accepted']and not x['resource_failure'];cu.append(x['cu'])
                else:assert x['cu_limit']==1000000 and x['cu']==1000000 and x['resource_failure']and not x['custom_rejection']
            else:assert not x['accepted']and x['custom_rejection']and not x['resource_failure']
    assert cu==expected[variant]
    reports[variant]={'status':'complete','cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
trace=j(e/'trace/analysis.json');tr=j(e/'trace/receipt.json');mi=j(e/'trace/mul-inventory.json')
assert trace['exact_text_match']and tr['clean_cu_equal']and trace['cu']==tr['result']['cu']==1212653
assert tr['proof_sha256']==proofs[0]and tr['source_manifest_sha256']==sha(e/'control/r18-stage.json')
assert mi['total']['calls']==1169 and mi['elf_sha256']==tr['elf_sha256']==trace['elf_sha256']
assert mi['trace_sha256']==sha(e/'trace/analysis.json')
names=['SamplerObservedCircleLoop','SamplerObservedCircleBridge','CachedFiniteSupport','SamplerObservedCircleProgram']
f=e/'lean/circle-final-a';records=j(f/'metadata.json');parent=j(root/'evidence/r80-qm31-observer/final/metadata.json')
assert records[:350]==parent and len(records)==354
deps=j(f/'dependency-pins.json');assert len(deps)==358
olddeps=j(root/'evidence/r80-qm31-observer/final/dependency-pins.json')
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
    elif '/aeneas-full/'in path:assert olddeps[path]==h,path
audits=[];formatter=[];formal={}
for r,n,count in zip(records[-4:],names,[2,3,3,4]):
    assert r['target_name']=='AspisV8R19/'+n and r['exit']==0
    assert r['base_revision']=='16c672f16becb0e1cbfeec350c01aa25277b24ba'
    src=root/'lean'/(r['target_name']+'.lean');assert sha(src)==r['source_sha256']
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',src.read_text())
    assert 'maxHeartbeats'not in src.read_text()and 'maxRecDepth'not in src.read_text()
    log=(f/(n+'.log')).read_text();assert 'sorryAx'not in log and 'error:'not in log and 'warning:'not in log
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log);assert len(got)==count
    for name,axs in got:
        axset={v.strip()for v in axs.split(',')};assert axset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
        audits.append(name)
        if 'core.fmt.Formatter'in axset:formatter.append(name)
    formal[n]=metrics(f/(n+'.log'));assert formal[n]['exit']==formal[n]['swaps']==0
assert len(audits)==12 and len(formatter)==8
res=j(f/'resources.json');assert [res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(5*2**30),str(7*2**30),'0','128']
receipt={'native':reports,'selected_research':'compose-a','security_promoted':False,'actual_1M_passed':False,
    'formal':{'targets':4,'theorem_audits':12,'metrics':formal,'axioms':audits,'formatter_dependent':formatter,
        'circle_view_matches_memoized_program':True,'arbitrary_prior_cache_retained':True,
        'concrete_SHA_ideality':False,'instrumentation_certified_compiler':False},
    'full_privacy':False,'full_soundness':False,
    'first_profile_obligation':'Universal actual-source C1/H1/G affine-image compatibility for the R84 two-swap profile, including all channel messages, adaptive prefixes and justified exceptions.',
    'next_observer':'Retain exact q22 source queries/rejections and compose the full shared-oracle source experiment, seed/commitments and visible publication/retries; do not infer independent conditional challenges from the cached interpreter law.'}
paths=[root/'lean/AspisV8R19'/(n+'.lean')for n in names]
paths += [root/'tools'/n for n in ['stage_r85_native.py','r85_private_ops.rs','r85_quotient.rs','run_r85_full.py','run_r85_lean.py','run_r85_trace.py','r85_mul_inventory.py','collect_r85_evidence.py','check_r85_evidence.py']]
paths += [root/'evidence/r84-bitperm/MANIFEST.json',root/'evidence/r80-qm31-observer/MANIFEST.json']
pins={str(p.relative_to(repo)):sha(p)for p in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(p.relative_to(e)):sha(p)for p in sorted(e.rglob('*'))if p.is_file()and p.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(p.relative_to(e))for p in e.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':expected['compose-a'],'formal_theorems':12,'full_privacy':False,'full_soundness':False,'artifacts':len(manifest)}))

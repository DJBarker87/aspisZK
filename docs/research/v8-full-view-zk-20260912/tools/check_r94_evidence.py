#!/usr/bin/env python3
"""Audit complete same-proof executions; reject attractive but slower products."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r94-native-products'
subprocess.run([sys.executable,str(root/'tools/check_r91_evidence.py')],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[-1]
    return {'exit':int(re.findall(r'Exit status: (\d+)',s)[-1]),'swaps':int(re.findall(r'Swaps: (\d+)',s)[-1]),
      'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
      'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[-1])}
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r91-wide-query-loop/wide-e/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
expected={'r92-sparse-a':[1131836,1130098],'r93-opening-a':[1130010,1128272],
 'r94-products-a':[1273103,1271360],'r94-products-b':[1164618,1162875]}
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
reports={}
for name,record in j(e/'collection.json')['variants'].items():
    d=e/name;m=j(d/'r18-stage.json');s=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*s.values(),*arts.values()]:blob(h)
    key={'r92-sparse-a':'r92_sparse','r93-opening-a':'r93_opening'}.get(name,'r94_products')
    v=m[key];parent=e/('control'if name=='r92-sparse-a'else'r92-sparse-a')/'r18-stage.json'
    assert v['control_manifest_sha256']==sha(parent)
    assert not v['protocol_changed']and not v['validation_removed']and not v['new_security_claim']
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(r['exit']==r['swaps']==0 for r in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            assert j(blob(h))=={'memory.high':str(hi*2**30),'memory.max':str(ma*2**30),'memory.swap.max':'0','pids.max':'128'}
    assert 'full_dual_chord_image_final_cases=64'in art('r24-host-a/compact-check.log').read_text()
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
    for run in svm['runs']:
        assert len(run['results'])==4
        for x in run['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['case']=='honest':
                if x['cu_limit']==100000000:assert x['accepted']and not x['resource_failure'];cu.append(x['cu'])
                else:assert x['cu_limit']==x['cu']==1000000 and x['resource_failure']and not x['custom_rejection']
            else:assert not x['accepted']and x['custom_rejection']and not x['resource_failure']and 'Custom(6)'in x['error']
    assert cu==expected[name]
    reports[name]={'status':'rejected_performance_regression'if name.startswith('r94')else'complete_research_winner',
        'cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
    if 'full-trace/analysis.json'in arts:
        t=j(art('full-trace/receipt.json'));an=j(art('full-trace/analysis.json'))
        assert t['clean_cu_equal']and t['elf_sha256']==svm['elf_sha256']and t['proof_sha256']==proofs[0]
        assert t['source_manifest_sha256']==sha(d/'r18-stage.json')and t['result']['cu']==cu[0]
        assert an['exact_text_match']and an['elf_sha256']==svm['elf_sha256']and an['cu']==cu[0]
        reports[name]['trace']={k:an[k]for k in ['executed_instructions','categories']}
        if name=='r94-products-a':assert next(x for x in an['functions']if '__multi3'in x['name'])['instructions']==92966
    if name.startswith('r94'):
        assert 'R94_PRODUCT full_products=262144 corner_cases=65536'in art('r24-host-a/r94-product-check.log').read_text()
    if name=='r93-opening-a':
        reuse=j(art('r24-host-a/compact-reuse.json'));assert not reuse['replayed']
        assert reuse['control_manifest_sha256']==sha(parent)
        assert reuse['log_sha256']==arts['r24-host-a/compact-check.log']
        cm=j(parent);changed=[n for n,h in m['files'].items()if cm['files'].get(n)!=h]
        assert changed==['docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs']
receipt={'variants':reports,'selected_research':'r93-opening-a','cu':expected['r93-opening-a'],
 'actual_1M_passed':False,'remaining_cu':130010,'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'new_lean_targets':0,'prior_formal_boundary':'R91 extracted query-loop output/state; public guard and complete observed shared-oracle history remain open.',
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for R84, including channel messages, adaptive/degenerate prefixes and justified exception losses.'}
paths=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|collect|check)_r9[234]_|r9[234]_)',f.name)and f.is_file()]
paths +=[root/'evidence/r91-wide-query-loop/MANIFEST.json',root/'tools/run_r85_trace.py',root/'tools/analyze_r24_full_trace.py']
pins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

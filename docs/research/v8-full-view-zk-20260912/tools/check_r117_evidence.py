#!/usr/bin/env python3
"""Audit whole native executions, source composition and retained failures."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r117-native-engine'
subprocess.run([sys.executable,str(root/'tools/check_r105_evidence.py')],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[-1]
    return {'exit':int(re.findall(r'Exit status: (\d+)',s)[-1]),'swaps':int(re.findall(r'Swaps: (\d+)',s)[-1]),
      'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
      'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[-1])}
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r105-native-auth/r105-parse/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
expected={
 'r106-terminal':[1048938,1048652],'r107-semantic':[1064587,1064343],
 'r108-decode':[1159096,1158855],'r109-geometry':[1061752,1061519],
 'r110-norm':[1062805,1062563],'r111-decode':[1072587,1072346],
 'r112-complex':[1055631,1055385],'r113-copy-b':[1054504,1054263],
 'r114-tag':[1061769,1061528],'r115-composed-b':[1016546,1016260],
 'r116-query':[1003633,1003365],'r117-primal':[999790,999532]}
failed={'r113-copy-a':'r24-host-a/r113-copy-check-compile.log',
        'r115-composed-a':'r24-host-a/r107-semantic-check-compile.log'}
markers={
 'r106-terminal':('compact-check.log','R106_TERMINAL profiles=512 geometry_coordinates=65536 inactive_coordinates=12160 malformed=3252'),
 'r107-semantic':('semantic-check.log','R107_SEMANTIC rounds=8192 basis_coordinates=221184 raw_boundary_cases=1044'),
 'r108-decode':('opening-check.log','R108_DECODE accepted_comparisons=32768 malformed=1807 offsets=8'),
 'r109-geometry':('compact-check.log','R109_GEOMETRY profiles=8192 scalar_coordinates=286720 malformed=84'),
 'r110-norm':('norm-check.log','R110_NORM arithmetic_profiles=65536 arithmetic_comparisons=393216 inversion_batches=512 zero_positions=132'),
 'r111-decode':('opening-check.log','R111_BIT_BASIS comparisons=37696 every_packed_bit=true offsets=8'),
 'r112-complex':('norm-check.log','R112_COMPLEX comparisons=69632 boundary_cartesian_cases=4096 malformed=6'),
 'r113-copy-b':('copy-check.log','R113_COPY raw_u32_gather_comparisons=2048 exact_integer_expansion=true all_selector_basis=true'),
 'r114-tag':('tag-check.log','R114_TAG raw_u32_coordinate_comparisons=30720'),
 'r116-query':('query-check.log','R116_QUERY profiles=2048 intermediate_prefix_checks=8192 independent_dense=64 malformed=642'),
 'r117-primal':('primal-check.log','R117_PRIMAL profiles=4096 folded_coordinates=44032 tail_stage_checks=1536 raw_boundary_cases=216')}
collection=j(e/'collection.json');reports={};manifests={};allarts={};receipts={};prefixes={}
assert not any(collection[k]for k in ['private_fixtures_collected','ELFs_collected','wallet_keys_collected','raw_registers_collected'])
for name,record in collection['variants'].items():
    d=e/name;m=j(d/'r18-stage.json');manifests[name]=m;s=j(d/'sources.json');arts=j(d/'artifacts.json');allarts[name]=arts
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*s.values(),*arts.values()]:blob(h)
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    for n,r in logs.items():assert r['swaps']==0 and r['exit']==(101 if failed.get(name)==n else 0),(name,n,r)
    for n,h in arts.items():
        if n.endswith('/resources.json')or n.endswith('/analysis-resources.json'):
            hi,ma=(1,2)if n.endswith('/analysis-resources.json')else(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith(('r24-svm','full-trace'))else(5,7)
            caps=j(blob(h));assert [caps[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
    commands=j(art('r24-host-a/commands.json'))
    assert all(x['exit']==(101 if 'r24-host-a/'+x['name']==failed.get(name)else 0)for x in commands)
    if name in failed:
        assert failed[name]in logs and not any(n.startswith(('r24-sbf','r24-svm'))for n in arts)
        assert ('cannot find macro `println`'if name=='r113-copy-a'else'unresolved module or unlinked crate `corelib`')in art(failed[name]).read_text()
        reports[name]={'status':'retained_host_compile_failure','CU_measured':False,'metrics':logs};continue
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    prefixes[name]=[[l for l in art(f'r24-host-a/world{w}.log').read_text().splitlines()if l.startswith('R19_PUBLIC_PREFIX ')]for w in range(2)]
    assert all(len(p)==1 for p in prefixes[name])
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==3281
    if name in markers:
        log,marker=markers[name];assert marker in art('r24-host-a/'+log).read_text(),name
    build=art('r24-sbf-a/compile.log').read_text()
    assert not any(x in build for x in ['overflows the maximum allowed frame','overwrites values in the frame'])
    assert 'all 1024 source permutation and inactive entries match SBF table'in build
    svm=j(art('r24-svm-a/receipt.json'));receipts[name]=svm
    assert svm['full_verifier']and not svm['security_promoted']and not svm['new_profile']
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['elf_sha256']==j(art('r24-sbf-a/environment.json'))['elf_sha256']
    sizes=j(d/'fixtures.json');assert [x['sha256']for x in sizes]==[x['proof_sha256']for x in svm['runs']]
    assert [x['sha256']for x in sizes]==[x['sha256']for x in pm['r105_native']['fixtures']]
    assert all(x['bytes']==57682 for x in sizes)
    cu=[];actual=[]
    for run in svm['runs']:
        assert len(run['results'])==4
        honest=[x for x in run['results']if x['case']=='honest'];assert len(honest)==2
        high=next(x for x in honest if x['cu_limit']==100000000)
        low=next(x for x in honest if x['cu_limit']==1000000)
        assert high['accepted']and not high['resource_failure'];cu.append(high['cu'])
        if high['cu']<1000000:
            assert low['accepted']and not low['resource_failure']and low['cu']==high['cu']
        else:assert not low['accepted']and low['resource_failure']and low['cu']==1000000
        actual.append(low['accepted'])
        for x in run['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['case']!='honest':assert x['case']=='bad-combined-final'and not x['accepted']and x['custom_rejection']and not x['resource_failure']and 'Custom(6)'in x['error']
    if name in expected:assert cu==expected[name]
    reports[name]={'status':'reject_regression'if name in ['r108-decode','r111-decode']else'retain_native_candidate',
      'cu':cu,'actual_1M_passed':actual,'proofs':sizes,'elf_sha256':svm['elf_sha256'],'metrics':logs}
    if name=='r115-composed-b':
        for trace in ['full-trace','full-trace-cap-b']:
            an=j(art(trace+'/analysis.json'));t=j(art(trace+'/receipt.json'))
            assert an['exact_text_match']and an['elf_sha256']==svm['elf_sha256']and an['cu']==cu[0]and t['clean_cu_equal']
        assert 'full-trace-cap-b/resources.json'in arts and 'full-trace-cap-b/analysis-resources.json'in arts
assert all(x==prefixes['r106-terminal']for x in prefixes.values()),'source public prefixes changed'
# Every changed native source is linked to an exact immediate predecessor.
for name,m in manifests.items():
    number=int(name[1:4]);key=f'r{number}_native'
    parent=('r110-norm'if number==112 else'r115-composed-b'if number==116 else'r116-query'if number==117 else None)
    old=manifests[parent]if parent else pm;path=e/parent/'r18-stage.json'if parent else e/'control/r18-stage.json'
    native=m[key];assert native['control_manifest_sha256']==sha(path)
    assert not any(native[k]for k in ['protocol_changed','validation_removed','security_promoted','new_security_claim'])
    assert sum(old['files'].get(n)!=h for n,h in m['files'].items())==native['changed']
for name in ['r115-composed-a','r115-composed-b']:
    for candidate in manifests[name]['r115_native']['candidates']:
        other=next(n for n,r in collection['variants'].items()if r['stage']==candidate['stage'])
        assert candidate['manifest_sha256']==sha(e/other/'r18-stage.json')
        assert candidate['receipt_sha256']==allarts[other]['r24-svm-a/receipt.json']
        assert candidate['isolated_cu']==reports[other]['cu']
        assert candidate['delta']==j(e/other/'sources.json')
    assert manifests[name]['r115_native']['isolated_savings_not_added']
selected='r117-primal'if max(reports['r117-primal']['cu'])<max(reports['r116-query']['cu'])else'r116-query'
cu=reports[selected]['cu'];passed=all(reports[selected]['actual_1M_passed'])
receipt={'native':reports,'selected_research':selected,'cu':cu,'actual_1M_passed':passed,
 'remaining_cu':max(0,max(cu)-1000000),'universal_CU_bound':False,
 'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'new_Lean_targets':0,'unchanged_formal_replay':False,
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for the two-swap sparse-G profile, including p0/p2 and all legal adaptive/degenerate prefixes or source-justified exceptional-event losses.',
 'additional_profile_obligation':'Eight-way commitment binding/hiding and exact-source shared-oracle composition; causal posterior simulation, seed/C2, retries/publication and coherent pre-beta quotient-pair extraction remain open.'}
paths=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|collect|check|analyze)_r(10[6-9]|11[0-7])_|r(10[6-9]|11[0-7])_)',f.name)and f.is_file()]
paths+=[root/'evidence/r105-native-auth/MANIFEST.json']
sourcepins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(sourcepins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==sourcepins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':cu,'actual_1M_passed':passed,'full_security':False,'artifacts':len(manifest)}))

#!/usr/bin/env python3
"""Audit authentication pilots separately from actual full-verifier results."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r105-native-auth'
subprocess.run([sys.executable,str(root/'tools/check_r100_evidence.py')],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[-1]
    return {'exit':int(re.findall(r'Exit status: (\d+)',s)[-1]),'swaps':int(re.findall(r'Swaps: (\d+)',s)[-1]),
      'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
      'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',s)[-1])}
def caps(f,hi,ma):
    r=j(f);assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r100-folded-query-observation/r99-fold-c/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
expected={'r102-auth':[1072399,1072158],'r103-words':[1080902,1078242],
 'r104-aligned':[1076876,1074216],'r104-inactive':[1074919,1074649],'r105-parse':[1066127,1065886]}
wire_counts={'r102-auth':3283,'r103-words':13316,'r104-aligned':13314,'r104-inactive':3282,'r105-parse':3282,'r105-gather':3282}
reports={};manifests={};allarts={}
collection=j(e/'collection.json')
assert not any(collection[k]for k in ['private_fixtures_collected','ELFs_collected','wallet_keys_collected','raw_registers_collected'])
for name,record in collection['variants'].items():
    d=e/name;m=j(d/record['manifest']);manifests[name]=m;s=j(d/'sources.json');arts=j(d/'artifacts.json');allarts[name]=arts
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*s.values(),*arts.values()]:blob(h)
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(r['exit']==r['swaps']==0 for r in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith(('sbf','r24-sbf'))else(2,3)if n.startswith(('svm','r24-svm','full-trace'))else(5,7)
            caps(blob(h),hi,ma)
    if name=='r101-auth':
        assert not m['full_verifier']and not m['actual_proof_fixtures']and not m['new_encoding_installed']
        check=art('host/check.log').read_text();assert 'independent_full_trees=true actual_proofs=false'in check
        svm=j(art('svm/receipt.json'));assert not svm['full_verifier']and not svm['under_1M_full_verifier']and not svm['security_promoted']
        assert svm['source_manifest_sha256']==sha(d/'r101-stage.json')
        auth_expected={2:[114620,118920],4:[76768,79451],8:[66854,70587]};summary=[]
        for run in svm['runs']:
            assert len(run['results'])==4
            for x in run['results']:
                assert x['cu_limit']in [1000000,100000000]and x['heap_bytes']==262144 and x['unchanged_accounts']
                if x['case']=='honest':assert x['accepted']and not x['resource_failure']and x['cu']==auth_expected[run['arity']][run['world']]
                else:assert x['case']=='bad-auth-root'and x['custom_rejection']and not x['resource_failure']and 'Custom(101)'in x['error']
            summary.append({'arity':run['arity'],'world':run['world'],'bytes':run['input_bytes'],'cu':run['results'][0]['cu']})
        reports[name]={'full_verifier':False,'auth_only':summary,'metrics':logs};continue
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==wire_counts[name]and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==wire_counts[name]-1
    if name in ['r102-auth','r103-words']:
        for w in range(2):
            log=art(f'r24-host-a/generate-world{w}.log').read_text()
            for marker in ['R17_H1_WITNESS_JOINT rank=540','R19_G_WITNESS_JOINT equations=626 rank=602',
                'R19_CHANNEL_WITNESS source_p0_p2_retained=true','R17_C1_WITNESS_VALIDATED same_public=true']:
                assert marker in log
    if name=='r102-auth':assert 'query_schedules=512 differential_cases=42772 max_frontier=658 attained=true'in art('r24-host-a/auth-check.log').read_text()
    if name in ['r103-words','r104-aligned']:
        assert 'R103_WORDS comparisons=4096 malformed=3201'in art('r24-host-a/word-check.log').read_text()
    if name=='r104-inactive':assert 'profiles=4096 scalar_comparisons=77824 malformed=1536'in art('r24-host-a/sum-check.log').read_text()
    if name=='r105-parse':assert 'accepted_comparisons=896 malformed=33645 offsets=4 fields=699'in art('r24-host-a/native-check.log').read_text()
    if name=='r105-gather':
        log=art('r24-host-a/native-check.log').read_text()
        assert 'old_terms=544 new_terms=544 exact_integer_map=true'in log
        assert 'source_terms=544 weight_checks=70720 scratch_and_full_lane_cases=512'in log
        assert not any(n.startswith(('r24-sbf','r24-svm'))for n in arts)
        reports[name]={'status':'stopped_after_host_no_terms_removed','CU_measured':False,'metrics':logs};continue
    build=art('r24-sbf-a/compile.log').read_text()
    assert not any(x in build for x in ['overflows the maximum allowed frame','overwrites values in the frame'])
    assert 'all 1024 source permutation and inactive entries match SBF table'in build
    svm=j(art('r24-svm-a/receipt.json'));assert svm['full_verifier']and not svm['security_promoted']
    assert svm['new_profile']==(name in ['r102-auth','r103-words'])
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
    assert svm['elf_sha256']==j(art('r24-sbf-a/environment.json'))['elf_sha256']
    sizes=j(d/'fixtures.json');assert [x['sha256']for x in sizes]==[x['proof_sha256']for x in svm['runs']]
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
    reports[name]={'status':'retain_research'if name in ['r102-auth','r105-parse']else'reject_regression',
      'cu':cu,'proofs':sizes,'elf_sha256':svm['elf_sha256'],'metrics':logs}
    if name=='r102-auth':
        an=j(art('full-trace/analysis.json'));t=j(art('full-trace/receipt.json'))
        assert an['exact_text_match']and an['elf_sha256']==svm['elf_sha256']and an['cu']==cu[0]and t['clean_cu_equal']
# Each child has a verifiable immediate parent, not just a loose base revision.
for child,parent,key,count in [('r102-auth',None,'r102_auth',9),('r103-words','r102-auth','r103_words',9),
 ('r104-aligned','r103-words','r104_native',1),('r104-inactive','r102-auth','r104_native',4),
 ('r105-parse','r102-auth','r105_native',4),('r105-gather','r102-auth','r105_native',3)]:
    m=manifests[child];old=pm if parent is None else manifests[parent]
    path=e/'control/r18-stage.json'if parent is None else e/parent/'r18-stage.json'
    assert m[key]['control_manifest_sha256']==sha(path)and not m[key]['security_promoted']
    assert sum(old['files'].get(n)!=h for n,h in m['files'].items())==count
    if key in ['r104_native','r105_native']:
        assert not m[key]['protocol_changed']and not m[key]['validation_removed']and not m[key]['new_security_claim']
        assert [x['sha256']for x in j(e/child/'fixtures.json')]==[x['sha256']for x in j(e/parent/'fixtures.json')]
receipt={'native':reports,'selected_research':'r105-parse','cu':expected['r105-parse'],'remaining_cu':66127,
 'actual_1M_passed':False,'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'new_Lean_targets':0,'unchanged_formal_replay':False,
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for the two-swap sparse-G profile, including p0/p2 and all legal adaptive/degenerate prefixes or source-justified exceptional-event losses.',
 'additional_profile_obligation':'Compose eight-way commitment binding/hiding and exact source oracle observations; then full causal posterior privacy, seed/C2 shared-oracle, visible retry/publication and coherent pre-beta quotient-pair extraction.'}
paths=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|collect|check)_r10[1-5]_|r10[1-5]_)',f.name)and f.is_file()]
paths +=[root/'evidence/r100-folded-query-observation/MANIFEST.json']
sourcepins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(sourcepins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==sourcepins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'remaining_cu':66127,'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

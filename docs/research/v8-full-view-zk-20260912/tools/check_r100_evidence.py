#!/usr/bin/env python3
"""Audit complete native runs and the selected q22 source/oracle bridge."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r100-folded-query-observation'
subprocess.run([sys.executable,str(root/'tools/check_r98_evidence.py')],stdout=subprocess.DEVNULL,check=True)
subprocess.run([sys.executable,str(root/'tools/generate_r100_query_observer.py')],stdout=subprocess.DEVNULL,check=True)
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
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r98-native-query-entry/r98-query-b/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
expected={'r99-fold-b':[1125817,1124003],'r99-fold-c':[1123090,1121361]}
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
reports={}
for name,record in j(e/'collection.json')['variants'].items():
    d=e/name;m=j(d/'r18-stage.json');s=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}and len(s)==9
    for h in [*s.values(),*arts.values()]:blob(h)
    v=m['r99_fold'];assert v['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not v['protocol_changed']and not v['validation_removed']and not v['new_security_claim']
    assert v.get('private_arithmetic',False)==(name=='r99-fold-c')
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(r['exit']==r['swaps']==0 for r in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith(('r24-svm','full-trace'))else(5,7)
            caps(blob(h),hi,ma)
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    assert 'profiles=4096 weights=174288 complete_folds=87144 zero_chords=306 malformed=132'in art('r24-host-a/fold-check.log').read_text()
    assert 'R85_QUOTIENT arbitrary_full_kernel_comparisons=8192'in art('r24-host-a/opening-check.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==3281
    build=art('r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame'not in build and 'overwrites values in the frame'not in build
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
    reports[name]={'status':'rejected_performance_regression'if name=='r99-fold-b'else'complete_research_winner','cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
    if name=='r99-fold-c':
        an=j(art('full-trace/analysis.json'));t=j(art('full-trace/receipt.json'))
        assert an['exact_text_match']and an['elf_sha256']==svm['elf_sha256']and an['cu']==cu[0]and t['clean_cu_equal']
final=e/'lean/final-a';records=j(final/'metadata.json')
assert records[:-4]==j(root/'evidence/r98-native-query-entry/lean/entry-final-a/metadata.json')and len(records)==368
formal={};audits=[];formatter=[]
for record,n,count in zip(records[-4:],['QueryObservedSource','QueryObservedBlock','QueryObservedExecution','QueryObservedProgram'],[0,4,4,4]):
    src=root/'lean/AspisV8R19'/(n+'.lean');log=final/(n+'.log');s=log.read_text()
    assert record['target_name']=='AspisV8R19/'+n and record['source_sha256']==sha(src)and record['exit']==0
    assert record['base_revision']=='059abfb388290177bbb1857745fc48e3ae9e3833'and record['toolchain']=='leanprover/lean4:v4.32.0'
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',src.read_text())
    assert not any(x in s for x in ['error:','warning:','sorryAx'])
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s);assert len(got)==count
    for name,axs in got:
        axset={v.strip()for v in axs.split(',')};assert axset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
        audits.append(name)
        if 'core.fmt.Formatter'in axset:formatter.append(name)
    formal[n]=metrics(log);assert formal[n]['exit']==formal[n]['swaps']==0
assert len(audits)==12 and len(formatter)==10;caps(final/'resources.json',5,7)
deps=j(final/'dependency-pins.json');olddeps={}
for f in(root/'evidence').rglob('dependency-pins.json'):
    if e not in f.parents:olddeps.update(j(f))
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
    elif '/aeneas-full/'in path:assert olddeps[path]==h,path
receipt={'native':reports,'cu':expected['r99-fold-c'],'selected_research':'r99-fold-c','remaining_cu':123090,
 'actual_1M_passed':False,'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'formal':{'targets':4,'theorem_audits':12,'formatter_dependent':formatter,'metrics':formal,
   'complete_selected_query_observation_proved':True,'cached_ideal_oracle_law_proved':True,
   'certified_instrumentation_compiler':False},
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for R84, including channel messages, adaptive/degenerate prefixes and justified exception losses.',
 'next_observer':'Compose the complete source experiment and its shared-oracle history, beyond the now separately proved circle and selected query samplers.'}
paths=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|generate|collect|check)_r(99|100)_|r99_)',f.name)and f.is_file()]
paths +=[root/'lean/AspisV8R19'/(n+'.lean')for n in ['QueryObservedSource','QueryObservedBlock','QueryObservedExecution','QueryObservedProgram']]
paths +=[root/'evidence/r98-native-query-entry/MANIFEST.json']
sourcepins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(sourcepins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==sourcepins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'formal_targets':4,'theorem_audits':12,'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

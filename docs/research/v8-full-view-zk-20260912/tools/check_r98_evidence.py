#!/usr/bin/env python3
"""Audit the native checkpoint and exact extracted selected query entry."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r98-native-query-entry'
subprocess.run([sys.executable,str(root/'tools/check_r94_evidence.py')],stdout=subprocess.DEVNULL,check=True)
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
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r94-native-products/r93-opening-a/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
expected={'r95-merkle-a':[1125130,1123392],'r96-square-a':[1125978,1124239],'r98-query-b':[1125129,1123391]}
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
reports={}
for name,record in j(e/'collection.json')['variants'].items():
    d=e/name;m=j(d/'r18-stage.json');s=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*s.values(),*arts.values()]:blob(h)
    key={'r95-merkle-a':'r95_merkle','r96-square-a':'r96_square','r97-opt2-a':'r97_profile'}.get(name,'r98_query')
    v=m[key];parent=e/('control'if name=='r95-merkle-a'else'r95-merkle-a')/'r18-stage.json'
    assert v['control_manifest_sha256']==sha(parent)
    assert not v['protocol_changed']and not v['validation_removed']and not v['new_security_claim']
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')};assert all(r['swaps']==0 for r in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            caps(blob(h),hi,ma)
    if name=='r98-query-a':
        assert 'crate::sumcheck'in art('r24-host-a/r98-query-check-compile.log').read_text()
        assert j(art('r24-host-a/commands.json'))[-1]['exit']==101 and 'r24-svm-a/receipt.json'not in arts
        reports[name]={'status':'retained_test_import_failure','metrics':logs};continue
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==3281
    build=art('r24-sbf-a/compile.log').read_text()
    if name=='r97-opt2-a':
        assert all(t in build for t in ['Estimated function frame size: 4352 bytes','Estimated function frame size: 4416 bytes','overwrites values in the frame','FAIL: frame diagnostic rejects this ELF'])
        assert j(art('r24-sbf-a/commands.json'))[-1]['exit']==1 and 'r24-svm-a/receipt.json'not in arts
        assert not j(art('r24-host-a/host-reuse.json'))['replayed']
        reports[name]={'status':'rejected_stack_gate','metrics':logs};continue
    assert all(r['exit']==0 for r in logs.values())
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
    reports[name]={'status':'rejected_performance_regression'if name=='r96-square-a'else'complete_research_winner','cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
    if name=='r95-merkle-a':
        assert 'honest_schedules=594 cases=8230 ordered_segmented_hash_calls_equal=true stateful_backend_equal=true'in art('r24-host-a/merkle-check.log').read_text()
        an=j(art('full-trace/analysis.json'));t=j(art('full-trace/receipt.json'))
        assert an['exact_text_match']and an['elf_sha256']==svm['elf_sha256']and an['cu']==cu[0]and t['clean_cu_equal']
    if name=='r96-square-a':assert 'R96_SQUARE cases=262144 corner_cases=256'in art('r24-host-a/r96-square-check.log').read_text()
    if name=='r98-query-b':assert 'public_calls=7128 guard_cases=1000096 ordered_hash_calls_equal=true stateful_backend_equal=true kat_pinned=true'in art('r24-host-a/query-check.log').read_text()
extract=e/'extraction';pins=j(extract/'source-pins.json');current=j(e/'r98-query-b/r18-stage.json')
assert pins['stage_manifest_sha256']==sha(e/'r98-query-b/r18-stage.json')
for n,h in pins['unchanged_source_files'].items():assert current['files']['crates/aspis-core/src/'+n]==h
for n,h in j(extract/'generated-pins.json').items():assert sha(extract/n)==h
assert all(r['exit']==0 for r in j(extract/'commands.json'));caps(extract/'resources.json',5,7)
subprocess.run([sys.executable,str(root/'tools/stage_r98_entry.py'),'--raw',str(extract/'generated/AspisR98Query'),'--sources',str(root/'lean'),'--check'],check=True,stdout=subprocess.DEVNULL)
assert not (extract/'generated/AspisR98Query/FunsExternal.lean').exists()
final=e/'lean/entry-final-a';records=j(final/'metadata.json')
assert records[:-2]==j(root/'evidence/r91-wide-query-loop/lean/query-final-a/metadata.json')and len(records)==364
formal={};audits=[];formatter=[]
for record,n,count in zip(records[-2:],['QueryEntrySource','QueryEntryExecution'],[0,4]):
    src=root/'lean/AspisV8R19'/(n+'.lean');log=final/(n+'.log');s=log.read_text()
    assert record['target_name']=='AspisV8R19/'+n and record['source_sha256']==sha(src)and record['exit']==0
    assert record['base_revision']=='da1110c9f49179292d332e1d300f618ba2d8f5d4'and record['toolchain']=='leanprover/lean4:v4.32.0'
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',src.read_text())
    assert not any(x in s for x in ['error:','warning:','sorryAx'])
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s);assert len(got)==count
    for name,axs in got:
        axset={v.strip()for v in axs.split(',')};assert axset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
        audits.append(name)
        if 'core.fmt.Formatter'in axset:formatter.append(name)
    formal[n]=metrics(log);assert formal[n]['exit']==formal[n]['swaps']==0
assert len(audits)==4 and len(formatter)==3;caps(final/'resources.json',5,7)
deps=j(final/'dependency-pins.json');olddeps={}
for f in(root/'evidence').rglob('dependency-pins.json'):
    if e not in f.parents:olddeps.update(j(f))
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
    elif '/aeneas-full/'in path:assert olddeps[path]==h,path
receipt={'native':reports,'cu':expected['r98-query-b'],'selected_research':'r98-query-b','remaining_cu':125129,
 'actual_1M_passed':False,'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'formal':{'targets':2,'theorem_audits':4,'formatter_dependent':formatter,'metrics':formal,
   'selected_public_guard_result_and_state_proved':True,'complete_observed_query_history_proved':False},
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for R84, including channel messages, adaptive/degenerate prefixes and justified exception losses.',
 'next_observer':'Instrument the exact public query entry, prove ordered shared-oracle history and memoized law, then compose the complete experiment.'}
paths=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|extract|collect|check)_r9[5678]_|r9[5678]_)',f.name)and f.is_file()]
paths +=[root/'lean/AspisV8R19'/(n+'.lean')for n in ['QueryEntrySource','QueryEntryExecution']]
paths +=[root/'evidence/r94-native-products/MANIFEST.json']
sourcepins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(sourcepins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==sourcepins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'formal_targets':2,'theorem_audits':4,'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

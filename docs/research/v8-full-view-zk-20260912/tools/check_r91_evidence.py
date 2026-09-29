#!/usr/bin/env python3
"""Audit R91's full execution, retained failures, and exact outer-loop boundary."""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r91-wide-query-loop'
subprocess.run([sys.executable,str(root/'tools/check_r90_evidence.py')],stdout=subprocess.DEVNULL,check=True)
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
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r90-native-query/r90-gamma-a/r18-stage.json')
for n,h in j(e/'control/sources.json').items():assert pm['files'][n]==h;blob(h)
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
reports={}
for name,record in j(e/'collection.json')['variants'].items():
    d=e/name;m=j(d/'r18-stage.json');s=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert len(m['files'])==record['pins']and set(pm['files'])<=set(m['files'])
    assert s=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*s.values(),*arts.values()]:blob(h)
    v=m['r91_wide'];assert v['control_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert not v['protocol_changed']and not v['validation_removed']and not v['new_security_claim']
    assert v['public_raw_constructor_fallback_retained']and v['overflow_checks_enabled']
    def art(n):return blob(arts[n])
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(r['swaps']==0 for r in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            caps(blob(h),hi,ma)
    if name=='wide-d':
        assert 'core::marker::Copy' in art('r24-host-a/r84-bitperm-check-compile.log').read_text()
        assert j(art('r24-host-a/commands.json'))[-1]['exit']==101
        assert 'r24-svm-a/receipt.json'not in arts
        reports[name]={'status':'retained_compile_failure','metrics':logs};continue
    assert 'canonical_pairs=265536 raw_operation_cases=392'in art('r24-host-a/r91-add-check.log').read_text()
    assert 'full_dual_chord_image_final_cases=64'in art('r24-host-a/compact-check.log').read_text()
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED'in art(f'r24-host-a/world{w}.log').read_text()
    wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
    assert sum(x['checked_rejection']for x in wire['cases'])==3281
    build=art('r24-sbf-a/compile.log').read_text()
    if name!='wide-e':
        assert 'Estimated function frame size: 6336 bytes'in build and 'FAIL: frame diagnostic rejects this ELF'in build
        assert j(art('r24-sbf-a/commands.json'))[-1]['exit']==1
        assert 'r24-svm-a/receipt.json'not in arts
        reports[name]={'status':'rejected_stack_gate','metrics':logs};continue
    assert all(r['exit']==0 for r in logs.values())
    assert 'overflows the maximum allowed frame'not in build and not('Stack offset'in build and 'exceeded'in build)
    assert 'all 1024 source permutation and inactive entries match SBF table'in build
    assert 'test result: ok. 10 passed; 0 failed;'in art('r91-recorder/test.log').read_text()
    assert j(art('r91-recorder/receipt.json'))=={'exit':0,'manifest_sha256':sha(d/'r18-stage.json')}
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
    assert cu==[1135747,1134007]
    reports[name]={'status':'complete_research_winner','cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
final=e/'lean/query-final-a';records=j(final/'metadata.json')
parent=j(root/'evidence/r90-native-query/lean/query-final-a/metadata.json')
assert records[:-3]==parent and len(records)==362
names=['AspisV8R19/'+n for n in ['QueryBlockWords','QueryBlockStep','QueryLoopExecution']]
formal={};audits=[];formatter=[]
for record,name,count in zip(records[-3:],names,[5,4,2]):
    assert record['target_name']==name and record['exit']==0 and record['toolchain']=='leanprover/lean4:v4.32.0'
    assert record['base_revision']=='8d84840936fb9338c71b045f527c065b691ba125'
    src=root/'lean'/(name+'.lean');assert sha(src)==record['source_sha256']
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',src.read_text())
    log=final/(Path(name).name+'.log');s=log.read_text()
    assert not any(x in s for x in ['error:','warning:','sorryAx'])
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s);assert len(got)==count
    for n,axs in got:
        axset={v.strip()for v in axs.split(',')};assert axset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
        audits.append(n)
        if 'core.fmt.Formatter'in axset:formatter.append(n)
    formal[name]=metrics(log);assert formal[name]['exit']==formal[name]['swaps']==0
assert len(audits)==11 and len(formatter)==4
caps(final/'resources.json',5,7)
deps=j(final/'dependency-pins.json');olddeps={}
for f in(root/'evidence').rglob('dependency-pins.json'):
    if e not in f.parents:olddeps.update(j(f))
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
    elif '/aeneas-full/'in path:assert olddeps[path]==h,path
receipt={'native':reports,'selected_research':'wide-e','cu':[1135747,1134007],
 'actual_1M_passed':False,'security_promoted':False,'full_privacy':False,'full_soundness':False,
 'formal':{'targets':3,'theorem_audits':11,'formatter_dependent':formatter,'metrics':formal,
   'actual_block_chunks':True,'outer_query_loop_value_and_state':True,
   'public_argument_guard_proved':False,'shared_oracle_query_history_proved':False},
 'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for R84, including channel messages, adaptive/degenerate prefixes and justified exception losses.',
 'next_observer':'Close the public power-of-two guard without admitting ctpop; connect ordered shared-oracle observations and compose the complete source experiment.'}
paths=[root/'lean'/(n+'.lean')for n in names]
paths +=[f for f in(root/'tools').iterdir()if re.match(r'((stage|run|collect|check)_r91_|r91_)',f.name)and f.is_file()]
paths +=[root/'evidence/r90-native-query/MANIFEST.json']
pins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'formal_targets':3,'formal_theorems':11,
 'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

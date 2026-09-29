#!/usr/bin/env python3
"""Audit exact native deltas, complete CU receipts and the bounded source loop."""
import argparse,ast,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r90-native-query'
subprocess.run([sys.executable,str(root/'tools/check_r85_evidence.py')],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[1]
    return {'exit':int(re.search(r'Exit status: (\d+)',s)[1]),'swaps':int(re.search(r'Swaps: (\d+)',s)[1]),
        'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
def caps(f,hi,ma):
    r=j(f);assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
pm=j(e/'control/r18-stage.json');assert pm==j(root/'evidence/r85-private-circle/compose-a/r18-stage.json')
original=j(e/'control/sources.json')
for n,h in original.items():assert h==pm['files'][n];blob(h)
variants=j(e/'collection.json')['variants'];manifests={n:j(e/n/'r18-stage.json')for n in variants}
proofs=['d0396cfbf2850540182bf7ed028a0739379cccb04439f5a61a3700989f8628cd','581b08936f5aaaea7f69d0cb1b324499779f40f1a2bf67dedc4a701462bc428d']
expected={'r86-merkle-c':[1187578,1185776],'r87-prepare-d':[1143400,1141596],
    'r88-align-a':[1166680,1164921],'r89-packed-a':[1147101,1145297],'r90-gamma-a':[1141057,1139217]}
ex='docs/research/v8-no-work-100-20260907/experiments/'
reports={}
for variant in variants:
    d=e/variant;m=manifests[variant];sources=j(d/'sources.json');arts=j(d/'artifacts.json')
    assert set(pm['files'])<=set(m['files']) and len(m['files'])==variants[variant]['pins']
    assert sources=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    for h in [*sources.values(),*arts.values()]:blob(h)
    key={'r86':'r86_native','r87':'r87_prepare','r88':'r88_alignment','r89':'r89_packed','r90':'r90_gamma'}[variant[:3]]
    v=m[key];control='control'if variant.startswith('r86')else 'r86-merkle-c'if variant.startswith('r87')else'r87-prepare-d'
    assert v['control_manifest_sha256']==sha(e/control/'r18-stage.json')
    assert not v['protocol_changed'] and not v['validation_removed'] and not v['new_security_claim']
    assert [f['sha256']for f in m['r85_native']['fixtures']]==proofs
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(v['swaps']==0 for v in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            caps(blob(h),hi,ma)
    def art(n):return blob(arts[n])
    if variant not in expected:
        assert 'r24-svm-a/receipt.json'not in arts
        if variant!='r87-prepare-a':assert any(r['exit']==101 for r in logs.values())
        else:assert not arts
        reports[variant]={'status':'stage_only'if not arts else'compile_failure_retained','metrics':logs};continue
    assert all(r['exit']==0 for r in logs.values())
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
    assert cu==expected[variant]
    reports[variant]={'status':'rejected_regression'if variant[:3]in ['r88','r89']else'complete_winner',
        'cu':cu,'elf_sha256':svm['elf_sha256'],'metrics':logs}
# Fixed public descriptor: reconstruct from the unchanged source-exported tables.
m=manifests['r87-prepare-d'];s=j(e/'r87-prepare-d/sources.json')
table_hash=m['files'][ex+'r17_basis_tables.rs']
assert table_hash==pm['files'][ex+'r17_basis_tables.rs']
parent=root/'evidence/r84-bitperm/compact'
table=next(blob2 for blob2 in [root/'evidence/r84-bitperm/blobs'/table_hash] if blob2.is_file()).read_text()
order=ast.literal_eval(re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',table)[1])
inactive=ast.literal_eval(re.search(r'INACTIVE: \[bool; 1024\] = (\[[^;]+\]);',table)[1].replace('true','True').replace('false','False'))
prefix=b'AV8/R84/functional/sparseG-bitperm-two-swaps/channel-fold/v2'+b''.join(r.to_bytes(2,'little')for r in order)+bytes(inactive)
assert len(prefix)==3132 and hashlib.sha256(prefix).hexdigest()==m['r87_prepare']['descriptor_prefix_sha256']
assert ast.literal_eval(blob(s[ex+'r87_descriptor.rs']).read_text().split('=&',1)[1].strip().rstrip(';'))==list(prefix)
assert blob(s[ex+'r17_compact_prepare.rs']).read_text().endswith((root/'tools/r87_prepare_pair.rs').read_text())
gamma=manifests['r90-gamma-a'];h=gamma['files'][ex+'shared_gamma.rs']
assert h==gamma['r90_gamma']['reused_kernel_sha256']==sha(repo/ex/'shared_gamma.rs')
assert 'independent_basis=580'in blob(j(e/'r90-gamma-a/artifacts.json')['r24-host-a/gamma-check.log']).read_text()
trace=j(e/'trace/analysis.json');tr=j(e/'trace/receipt.json');mi=j(e/'trace/mul-inventory.json')
assert trace['exact_text_match']and tr['clean_cu_equal']and trace['cu']==tr['result']['cu']==1143400
assert tr['proof_sha256']==proofs[0]and tr['source_manifest_sha256']==sha(e/'r87-prepare-d/r18-stage.json')
assert mi['total']['calls']==879 and mi['trace_sha256']==sha(e/'trace/analysis.json')
assert mi['elf_sha256']==tr['elf_sha256']==trace['elf_sha256']==reports['r87-prepare-d']['elf_sha256']
# Extraction is original Rust plus only the selected public entry; templates
# are retained as evidence of the open guard, never imported by the proof.
for suffix in 'ab':
    d=e/'extraction'/suffix;pins=j(d/'source-pins.json');sources=j(d/'sources.json')
    assert j(d/'r18-stage.json')==pm and pins['stage_manifest_sha256']==sha(e/'control/r18-stage.json')
    assert pins['base_revision']=='b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4'
    for n,h in pins['unchanged_source_files'].items():
        assert pm['files']['crates/aspis-core/src/'+n]==h
        text=blob(sources[n]).read_text()
        if n=='lib.rs':assert text==blob(original['crates/aspis-core/src/lib.rs']).read_text()+pins['lib_append']
        else:assert sha(blob(sources[n]))==h
    assert all(r['exit']==0 for r in j(d/'commands.json'));caps(d/'resources.json',5,7)
    for n,h in j(d/'generated-pins.json').items():blob(h)
    llbc=j(d/'llbc.json');assert llbc['sha256']==llbc['blob'];blob(llbc['blob'])
raw=j(e/'extraction/a/generated-pins.json')
for name in ['Types','Funs']:
    text=blob(raw['generated/AspisR86Query/'+name+'.lean']).read_text()
    if name=='Funs':
        marker='/-- [aspis_core::transcript::{aspis_core::transcript::Transcript}::challenge_queries_without_replacement]:\n'
        assert text.count(marker)==1
        text=text[:text.index(marker)]+'end AspisR86Query\n'
        text=text.replace('import AspisR86Query.FunsExternal\n','')
    text=text.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes\n')
    assert text==(root/'lean/AspisR86Query'/('Loops.lean'if name=='Funs'else'Types.lean')).read_text()
    assert not re.search(r'\b(axiom|sorry|admit)\b',text)
final=e/'lean/query-final-a';records=j(final/'metadata.json');parent=j(root/'evidence/r85-private-circle/lean/circle-final-a/metadata.json')
assert records[:354]==parent and len(records)==359
names=['AspisR86Query/Types','AspisR86Query/Loops',*['AspisV8R19/'+n for n in ['QueryChunkExecution','QueryChunkModel','QueryChunkSource']]]
audits=[];formatter=[];formal={}
for record,name,count in zip(records[-5:],names,[0,0,6,4,2]):
    assert record['target_name']==name and record['exit']==0 and record['toolchain']=='leanprover/lean4:v4.32.0'
    assert record['base_revision']=='b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4'
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
assert len(audits)==12 and len(formatter)==3
caps(final/'resources.json',5,7)
deps=j(final/'dependency-pins.json');olddeps={}
for f in (root/'evidence').rglob('dependency-pins.json'):
    if e not in f.parents:olddeps.update(j(f))
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
    elif '/aeneas-full/'in path:assert olddeps[path]==h,path
receipt={'native':reports,'selected_research':'r90-gamma-a','cu':expected['r90-gamma-a'],
    'actual_1M_passed':False,'security_promoted':False,'full_privacy':False,'full_soundness':False,
    'formal':{'targets':5,'theorem_audits':12,'formatter_dependent':formatter,'metrics':formal,
        'actual_inner_query_loop':True,'public_argument_guard_proved':False,
        'outer_query_loop_proved':False,'shared_oracle_query_history_proved':False},
    'first_profile_obligation':'Universal actual-source C1/H1/G joint affine-image compatibility for R84, including channel messages, adaptive/degenerate prefixes and justified exception losses.',
    'next_observer':'Identify actual 32-byte chunks and outer query history; close the public power-of-two guard without admitting the opaque template; compose the complete source experiment.'}
paths=[root/'lean'/(n+'.lean')for n in names]
paths += [f for f in (root/'tools').iterdir()if re.match(r'(extract|stage|run|collect|check)_r(86|87|88|89|90)_|r(86|87)_',f.name)and f.is_file()]
paths += [root/'evidence/r85-private-circle/MANIFEST.json',repo/ex/'shared_gamma.rs',repo/ex/'SharedGammaDots.lean']
pins={str(f.relative_to(repo)):sha(f)for f in sorted(paths)}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS_SCOPED','cu':receipt['cu'],'formal_targets':5,'formal_theorems':12,
    'actual_1M_passed':False,'full_security':False,'artifacts':len(manifest)}))

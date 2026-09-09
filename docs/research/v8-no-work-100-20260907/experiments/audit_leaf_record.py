#!/usr/bin/env python3
"""Check measured leaf-record control against the committed Merkle winner."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
EX=ROOT/'experiments'; EV=ROOT/'evidence/leaf-record'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_merkle_input.py'))
check,summary=prior['check'],prior['summary']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def pinned_sha(name):
    path='docs/research/v8-no-work-100-20260907/experiments/'+name
    return hashlib.sha256(subprocess.check_output(['git','show',
        '7ccf84a3b8c66c30a9db96fb9cb305849b65106b:'+path],cwd=EX)).hexdigest()
def load(folder,count):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==count,(folder,len(rows))
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=load('leaf-record-max-v1',24)
base=prior['sets']['both']; before=summary(base); current=summary(maximum)
deltas={}
for shape,xs in current['shapes'].items():
    ys=before['shapes'][shape]
    assert [x['proof_sha256'] for x in xs]==[x['proof_sha256'] for x in ys]
    assert all(x['body']==40282 for x in xs)
    deltas[shape]=[y['cu']-x['cu'] for x,y in zip(xs,ys)]
ordinary=load('leaf-record-ordinary-v1',24)
rollback=load('leaf-record-rollback-v1',2)
raw=maximum['withdrawal-255-2-success']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    for key,x in rows.items():
        assert x['artifacts']['selected_verifier']['sha256']==raw['artifacts']['selected_verifier']['sha256']
        assert x['fixture']['proof_sha256']==old[key]['fixture']['proof_sha256']
        for role in ('pool','registry','token_program'): assert x['artifacts'][role]==old[key]['artifacts'][role]
        for field in ('outcome','error'): assert x['execution'][field]==old[key]['execution'][field]
        if rows is rollback: assert x['execution']['selected_verifier_cpi_observed_in_logs']
lean=(EX/'leaf-record-lean.log').read_text()
assert sha(EX/'LeafRecord.lean') in lean
assert 'error:' not in lean and 'sorryAx' not in lean
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axs)==5
assert all(set(a.split(', ')) <= {'propext','Classical.choice','Quot.sound'} for _,a in axs)
oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',lean)
assert len(oleans)==2
if (EX/'LeafRecord.olean').exists(): assert sha(EX/'LeafRecord.olean')==oleans[-1]
resources={}
for job in ('test','sbf-build'):
    path=EV/f'leaf-record-{job}-v1.log'; log=path.read_text()
    assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
    if job=='test':
        assert '2 passed; 0 failed' in log
        assert pinned_sha('relation_callback.rs') in log and pinned_sha('leaf_record.rs') in log
    parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
    resources[job]={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
        'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
    assert resources[job]['swaps']==0
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
out={'schema':'aspis.research.leaf-record.v1','base_revision':'74f9b7661bad35374744b04a642ac1ccbb0d3580',
    'maximum':current,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':len(rollback),
    'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
    'elf_delta_bytes':raw['artifacts']['selected_verifier']['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
    'resources':resources,'stack_audit':stack,
    'lean':{'source_sha256':sha(EX/'LeafRecord.lean'),'olean_sha256':oleans[-1],
        'axioms':dict(axs),'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',lean)[1])},
    'source_sha256':{p:pinned_sha(p) for p in ('relation_callback.rs','leaf_record.rs')},
    'hash_input':{'bytes':220,'old_lengths':[2,186,32],'new_lengths':[2,218],
        'syscall_cu_each':204,'hash_calls_changed':False,'new_proof_or_transcript_bytes':0,
        'backend_requirement':'SHA backend hashes concatenation; same source audit as MerkleInput.'},
    'body_maximum':697*16+52+24+22*621+2*296*26,'extra_heap_bytes':0,
    'grinding_credit_bits':0,'universal_cu_bound':None,'global_security_certificate':None}
out['worst_observed_cu']=max(x['cu'] for xs in current['shapes'].values() for x in xs)
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-
    (max(x['cu'] for x in before['shapes'][s])-prior['out']['excess_over_same_pool_v7'][s])
    for s,xs in current['shapes'].items()}
out['selected']=all(v>0 for xs in deltas.values() for v in xs)
print(json.dumps(out,indent=2))

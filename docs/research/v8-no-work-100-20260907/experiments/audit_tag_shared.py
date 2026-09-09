#!/usr/bin/env python3
"""Recheck archived full-transaction outcomes and source-pinned proof evidence."""
import contextlib,hashlib,io,json,re,runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_tag_split.py'))
check,summary=prior['check'],prior['summary']
def load(path,count):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted(path.glob('*.json'))}
    assert len(rows)==count,(path,len(rows))
    return rows
maximum=load(ROOT/'evidence/tag-shared/tag-shared-max-v1',24)
ordinary=load(ROOT/'evidence/tag-shared/tag-shared-ordinary-v1',24)
rollback=load(ROOT/'evidence/tag-shared/tag-shared-rollback-v1',2)
old=load(ROOT/'evidence/tag-split/copy-tag-bounded-max-v1',24)
old_o=load(ROOT/'evidence/tag-split/copy-tag-bounded-ordinary-v1',24)
ms=summary(maximum);base=summary(old);savings={}
for shape,values in ms['shapes'].items():
    b=base['shapes'][shape]
    assert [x['proof_sha256'] for x in values]==[x['proof_sha256'] for x in b]
    assert all(x['body']==40282 for x in values)
    savings[shape]=[a['cu']-x['cu'] for a,x in zip(b,values)]
for rows,prev in ((maximum,old),(ordinary,old_o)):
    for key,x in rows.items():
        assert x['execution']['txv1_declared_compute_unit_limit']==1200000
        for role in ('pool','registry'):
            assert x['artifacts'][role]['sha256']==prev[key]['artifacts'][role]['sha256']
        assert x['artifacts']['token_program']==prev[key]['artifacts']['token_program']
        assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant']=='legacy35'
        for field in ('outcome','error'):
            assert x['execution'][field]==prev[key]['execution'][field]
for x in rollback.values():
    assert x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['scenario']=='withdrawal-cpi-failure'
    assert x['execution']['txv1_declared_compute_unit_limit']==1200000
for rows in (ordinary,rollback):
    for x in rows.values():
        assert x['artifacts']['selected_verifier']['sha256']==ms['artifact_hashes']['selected_verifier']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
leaves=[]
for stem,name,count in (('CopyTagSplit','split-cache',10),('CopyTagShared','interface-lean',4),('CopyTagSums','sums-lean',31)):
    path=EX/f'tag-shared-{name}.log';log=path.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    assert sha(EX/f'{stem}.lean') in log
    oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',log)
    assert len(oleans)==2
    if (EX/f'{stem}.olean').exists():assert sha(EX/f'{stem}.olean')==oleans[-1]
    axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    assert len(axs)==count
    assert all(set(a.split(', ')) <= {'propext','Classical.choice','Quot.sound'} for _,a in axs)
    leaves.append({'source':f'experiments/{stem}.lean','source_sha256':sha(EX/f'{stem}.lean'),
        'olean_sha256':oleans[-1],'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',log)[1]),'axioms':dict(axs),'log':str(path.relative_to(ROOT))})

resources={}
for name in ('test','sbf-build'):
    p=ROOT/'evidence/tag-shared'/f'tag-shared-{name}.log';log=p.read_text()
    assert '\tExit status: 0' in log
    assert not re.search(r'Stack offset .* exceeded|error:',log)
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1]
    parts=list(map(float,wall.split(':')))
    resources[name]={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
        'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(p.relative_to(ROOT))}
    assert resources[name]['swaps']==0
raw=maximum['withdrawal-255-2-success']
prep=(ROOT/'evidence/tag-shared/tag-shared-prepare.log').read_text()
hashes=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.rs',prep)
assert len(hashes)==2 and hashes[-1]==sha(EX/'copy_tag_shared_generated.rs')
out={'schema':'aspis.research.tag-shared.v1','base_revision':'50186b8ba739e0f0a0fb141ef19265c91b9e605a',
    'maximum':ms,'ordinary':summary(ordinary),'rollback_cases':len(rollback),'same_proof_savings_cu':savings,
    'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
    'lean':leaves,'resources':resources,'generator_sha256':sha(EX/'generate_tag_shared.py'),
    'copy_source_sha256':hashes[0],'generated_rust_sha256':hashes[1],
    'artifacts':{role:raw['artifacts'][role] for role in ('selected_verifier','pool','registry','token_program')},
    'body_maximum':40282,'new_proof_or_transcript_bytes':0,'extra_heap_bytes':0,
    'global_security_certificate':None,'universal_cu_bound':None,'grinding_credit_bits':0,
    'scope':'Universal generated ring identities and reduced-sum/range model; actual Rust differential and SBF tests; not translated Rust/compiler equivalence.'}
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-prior['v7'][s][0]['cu'] for s,xs in ms['shapes'].items()}
assert all(n>0 for xs in savings.values() for n in xs)
print(json.dumps(out,indent=2))

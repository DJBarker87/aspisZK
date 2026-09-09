#!/usr/bin/env python3
"""Replay retained evidence, not the expensive transaction or Lean suites."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; EX=ROOT/'experiments'; EV=ROOT/'evidence/auth-order'
REV='8e7e177f9ef4031dc1651ccb8f779efb7681ab27'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_decode_controls.py'))
check,summary=prior['check'],prior['summary']
base=prior['sets']['decode-blocks']; bs=summary(base)
def sha(data): return hashlib.sha256(data).hexdigest()
def load(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=load('auth-order-max-v1',24); ordinary=load('auth-order-ordinary-v1',24)
rollback=load('auth-order-rollback-v1',2); raw=maximum['withdrawal-255-2-success']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    for key,x in rows.items():
        assert x['fixture']['proof_sha256']==old[key]['fixture']['proof_sha256']
        assert x['artifacts']['selected_verifier']==raw['artifacts']['selected_verifier']
        for role in ('pool','registry','token_program'): assert x['artifacts'][role]==old[key]['artifacts'][role]
        for field in ('outcome','error'): assert x['execution'][field]==old[key]['execution'][field]
        if rows is rollback: assert x['execution']['selected_verifier_cpi_observed_in_logs']
ms=summary(maximum)
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
assert all(d>0 for ds in deltas.values() for d in ds)
# Reconstruct measured callback in memory from a literal patch, independent of
# later callback edits. No checkout/reset of concurrent source is performed.
text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'],cwd=ROOT).decode()
old=[];new=[];active=False
def replace(text,old,new):
    old=''.join(old);new=''.join(new)
    assert old and text.count(old)==1
    return text.replace(old,new,1)
for line in (EX/'auth-order-control.patch').read_text().splitlines(keepends=True):
    if line.startswith('@@'):
        if active: text=replace(text,old,new)
        old=[];new=[];active=True
    elif active:
        if line[0] in ' -': old.append(line[1:])
        if line[0] in ' +': new.append(line[1:])
assert active
callback_sha=sha(replace(text,old,new).encode()); kernel_sha=sha((EX/'auth_order.rs').read_bytes())
resources={}
for job in ('test','sbf-build'):
    path=EV/f'auth-order-{job}-v1.log'; log=path.read_text()
    assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
    if job=='test':
        assert '2 passed; 0 failed' in log and callback_sha in log and kernel_sha in log
    parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
    resources[job]={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
        'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
    assert resources[job]['swaps']==0
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
lean=(EX/'auth-order-final-lean.log').read_text(); failed=(EX/'auth-order-lean.log').read_text()
assert sha((EX/'AuthOrder.lean').read_bytes()) in lean
assert 'error:' not in lean and 'sorryAx' not in lean and 'error:' in failed
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",lean)
assert len(axs)==6 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
oleans=re.findall(r'([a-f0-9]{64})\s+[^\n]+\.olean',lean)
assert len(oleans)==2
if (EX/'AuthOrder.olean').exists(): assert sha((EX/'AuthOrder.olean').read_bytes())==oleans[-1]
out={'schema':'aspis.research.auth-order.v1','base_revision':REV,'maximum':ms,'same_proof_savings_cu':deltas,
    'ordinary':summary(ordinary),'rollback_cases':len(rollback),'selected':True,
    'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
    'elf_delta_bytes':raw['artifacts']['selected_verifier']['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
    'source_sha256':{'relation_callback.rs':callback_sha,'auth_order.rs':kernel_sha},
    'resources':resources,'stack_audit':stack,
    'lean':{'source_sha256':sha((EX/'AuthOrder.lean').read_bytes()),'olean_sha256':oleans[-1],'axioms':dict(axs),
        'exit':0,'wall_seconds':float(re.search(r'([\d.]+) real',lean)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',lean)[1]),'swaps':int(re.search(r'(\d+)  swaps',lean)[1])},
    'failed_preflight':{'exit':1,'log':'experiments/auth-order-lean.log','retained_claimed_proof':False,
        'reason':'List.Pairwise.imp has implicit element arguments; removed two explicit lambda binders.',
        'wall_seconds':float(re.search(r'([\d.]+) real',failed)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',failed)[1]),'swaps':int(re.search(r'(\d+)  swaps',failed)[1])},
    'descriptor_stack_payload_bytes':22*8,'extra_heap_bytes':0,'hash_count_change':0,
    'hash_backend_requirement':'Pure function of each leaf preimage, not arbitrary stateful HashFn; actual SHA backend source audit reused.',
    'query_scalar_order_changed':False,'body_maximum':697*16+52+24+22*621+2*296*26,
    'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,
    'global_security_certificate':None,'universal_cu_bound':None}
out['worst_observed_cu']=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()}
print(json.dumps(out,indent=2))

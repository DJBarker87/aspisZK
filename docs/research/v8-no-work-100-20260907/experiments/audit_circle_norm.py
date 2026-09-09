#!/usr/bin/env python3
"""Replay exact local evidence; this performs no SBF/prover/formal builds."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent; EX=ROOT/'experiments'; EV=ROOT/'evidence/circle-norm'
REV='b082d32c3deec5a4b48f4ceba41e44d167b2278b'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_chord_norm.py'))
check,summary=prior['check'],prior['summary']; base=prior['maximum']; bs=summary(base)
def sha(data): return hashlib.sha256(data).hexdigest()
def load(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=load('circle-norm-max-v1',24); ordinary=load('circle-norm-ordinary-v1',24)
rollback=load('circle-norm-rollback-v2',2); raw=maximum['withdrawal-255-2-success']
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
# Literal private-constructor/caller patch from the actual clean checkpoint.
text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'],cwd=ROOT).decode()
old=[];new=[];active=False
def replace(text,old,new):
    old=''.join(old);new=''.join(new);assert old and text.count(old)==1
    return text.replace(old,new,1)
for line in (EX/'circle-norm-control.patch').read_text().splitlines(keepends=True):
    if line.startswith('@@'):
        if active: text=replace(text,old,new)
        old=[];new=[];active=True
    elif active:
        if line[0] in ' -': old.append(line[1:])
        if line[0] in ' +': new.append(line[1:])
assert active
callback_sha=sha(replace(text,old,new).encode())
kernel_sha=sha(subprocess.check_output(['git','show','09a6dd7aa188b31dd96c898e9b3f5ae296514a70:docs/research/v8-no-work-100-20260907/experiments/circle_norm.rs'],cwd=ROOT))
points_sha=sha((EX/'circle-window-points.json').read_bytes())
resources={}
for job in ('test','sbf-build'):
    path=EV/f'circle-norm-{job}-v1.log'; log=path.read_text()
    assert '\tExit status: 0' in log and not re.search(r'Stack offset .* exceeded|error:',log)
    if job=='test':
        assert '1 passed; 0 failed' in log and callback_sha in log and kernel_sha in log and points_sha in log
        assert 'unit_domain_indices=262144 chord_profiles=1024' in log
        assert 'zero_denominators_reject=true off_circle_counterexample=true' in log
    parts=list(map(float,re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1].split(':')))
    resources[job]={'exit':0,'wall_seconds':sum(x*60**i for i,x in enumerate(reversed(parts))),
        'rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log)[1]),
        'swaps':int(re.search(r'Swaps: (\d+)',log)[1]),'log':str(path.relative_to(ROOT))}
    assert resources[job]['swaps']==0
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
leans={}
for name,logname in [('CircleNorm','circle-norm-lean.log'),('CircleNormTables','circle-norm-tables-final-lean.log')]:
    log=(EX/logname).read_text(); source=(EX/(name+'.lean')).read_bytes()
    assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
    assert not re.search(rb'\b(sorry|axiom)\b',source)
    axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    axs += [(x,'') for x in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(axs)==6 and all(set(a.split(', '))-set([''])<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
    olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/'+name+r'\.olean',log)[-1]
    if (EX/(name+'.olean')).exists(): assert sha((EX/(name+'.olean')).read_bytes())==olean
    leans[name]={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
        'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
    assert leans[name]['swaps']==0
# Exact table snapshot is checked against the compiled Rust public arrays by
# the test; all192 field predicates are kernel-checked, without a domain replay.
tables=json.loads((EX/'circle-window-points.json').read_text())
assert list(tables)==['low','middle','high']
for table in tables.values():
    assert len(table)==64
    assert all(0<=x<2147483647 and 0<=y<2147483647 and (x*x+y*y)%2147483647==1 for x,y in table)
subprocess.run(['python3',str(EX/'generate_circle_norm_tables.py'),'--check'],check=True)
testlog=(EV/'circle-norm-test-v1.log').read_text()
source_pins={'build.rs':'7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d',
    'circle_fri.rs':'77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b'}
assert all(h in testlog for h in source_pins.values())
model={'cm_squares':6,'cm_products':6,'cm_base_scalings':22*4,'point_base_products':22*2,
    'additional_setup_cm_add_sub':2,'previous_base_products':322,'new_base_products':256,'base_products_saved':66}
out={'schema':'aspis.research.circle-norm.v1','base_revision':REV,'maximum':ms,'same_proof_savings_cu':deltas,
    'ordinary':summary(ordinary),'rollback_cases':len(rollback),'selected':True,
    'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
    'elf_delta_bytes':raw['artifacts']['selected_verifier']['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
    'source_sha256':{'relation_callback.rs':callback_sha,'circle_norm.rs':kernel_sha,'circle-window-points.json':points_sha,**source_pins},
    'resources':resources,'lean':leans,'stack_audit':stack,'operation_model':model,
    'coefficient_payload_bytes':40,'norm_vector_payload_bytes':704,'allocator_peak_delta_bytes':None,
    'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,
    'point_precondition':'Private Selected constructor calls the pinned log20 source; 192 compiled table entries match kernel-checked snapshot. No public point/hint input.',
    'refinement_status':'Kernel-checked algebra and source-shaped table constructor; exact differential tests, not translated Rust/LLVM/SBF.',
    'global_security_certificate':None,'universal_cu_bound':None,'prover_time_delta_seconds':None}
out['worst_observed_cu']=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()}
print(json.dumps(out,indent=2))

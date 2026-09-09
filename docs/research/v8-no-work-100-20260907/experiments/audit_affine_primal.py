#!/usr/bin/env python3
"""Audit literal constant injection and the complete quiet affine-fold control."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/affine-primal'
REV='a955be1c158578057fed1840ed9f005cb3f1a18b'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_quotient_fold.py'))
    inversion=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(data):return hashlib.sha256(data).hexdigest()
text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'],cwd=ROOT).decode()
old=[];new=[];active=False
def replace(text,old,new):
    old=''.join(old);new=''.join(new);assert old and text.count(old)==1
    return text.replace(old,new,1)
for line in (EX/'affine-primal-callback.patch').read_text().splitlines(keepends=True):
    if line.startswith('@@'):
        if active:text=replace(text,old,new)
        old=[];new=[];active=True
    elif active:
        if line[0] in ' -':old.append(line[1:])
        if line[0] in ' +':new.append(line[1:])
assert active
src={**prior['out']['source_sha256'],'relation_callback.rs':sha(replace(text,old,new).encode()),
     'affine_primal.rs':sha((EX/'affine_primal.rs').read_bytes())}
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('affine-primal-max-v1',24);ordinary=evidence('affine-primal-ordinary-v1',24)
rollback=evidence('affine-primal-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    inversion['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
test=(EV/'affine-primal-test-v1.log').read_text()
assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
assert 'arbitrary_products=4096 complete_three_passes=256 chunk_lengths=15 maximal_channels=true zero_challenges=true' in test
assert '--cfg v8_qm_channel_partial' in test and '--cfg v8_range_dots' in test
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
log=(EX/'affine-primal-final-lean.log').read_text();source=(EX/'AffinePrimal.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==9 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/AffinePrimal\.olean',log)[-1]
if (EX/'AffinePrimal.olean').exists():assert sha((EX/'AffinePrimal.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.affine-primal.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,'resources':{j:inversion['resource'](EV/('affine-primal-'+j+'-v1.log')) for j in ('test','sbf-build')},
     'lean':lean,'stack_audit':stack,
     'operation_model':{'groups':64+16+4,'canonical_m31_adds_removed':4*(64+16+4),
        'raw_u64_adds_inserted_before_common_subexpression_elimination':9*(64+16+4),'new_m31_products':0,'new_reduction_channels':0,
        'new_heap_allocations':0},
     'range':{'channel_max':3*(2147483647-1)**2+4*(2147483647-1),'word_bound':2**64},
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked literal nine-channel injection/cast and integer-prefix bounds; selected source tests and complete outcomes, not translated Rust/LLVM/SBF.'}
assert out['range']['channel_max']<out['range']['word_bound']
print(json.dumps(out,indent=2))

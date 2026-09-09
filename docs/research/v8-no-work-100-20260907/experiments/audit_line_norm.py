#!/usr/bin/env python3
"""Audit the shared-line control against the exact selected split-inverse ELF."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/line-norm'
REV='992288fd577f647c810a506fc83b4811fb90f0e6'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(data):return hashlib.sha256(data).hexdigest()
def patched(name):
    text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/'+name],cwd=ROOT).decode()
    old=[];new=[];active=False
    def replace(text,old,new):
        old=''.join(old);new=''.join(new);assert old and text.count(old)==1
        return text.replace(old,new,1)
    for line in (EX/('line-norm-'+name.replace('.rs','')+'.patch')).read_text().splitlines(keepends=True):
        if line.startswith('@@'):
            if active:text=replace(text,old,new)
            old=[];new=[];active=True
        elif active:
            if line[0] in ' -':old.append(line[1:])
            if line[0] in ' +':new.append(line[1:])
    assert active
    return sha(replace(text,old,new).encode())
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('line-norm-max-v1',24);ordinary=evidence('line-norm-ordinary-v1',24)
rollback=evidence('line-norm-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    prior['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
src={name:patched(name) for name in ('relation_callback.rs','circle_norm.rs','joined_inverse.rs')}
src['line_norm.rs']=sha((EX/'line_norm.rs').read_bytes())
test=(EV/'line-norm-test-v1.log').read_text()
assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
assert 'chord_profiles=1024 arbitrary_point_profiles=512 lengths=1..22' in test
assert 'mismatched_line_counterexample=true half_boundary_tests=9 zero_and_shape_rejection=true' in test
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
log=(EX/'line-norm-final-lean.log').read_text();source=(EX/'LineNorm.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==10 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/LineNorm\.olean',log)[-1]
if (EX/'LineNorm.olean').exists():assert sha((EX/'LineNorm.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.line-norm.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,'resources':{job:prior['resource'](EV/('line-norm-'+job+'-v1.log')) for job in ('test','sbf-build')},
     'lean':lean,'stack_audit':stack,
     'operation_model':{'m31_squares_saved':22,'additional_setup_cm_half':1,'additional_setup_cm_add':1,
        'new_line_allocations':0,'additional_borrowed_line_slice':1,'additional_length_guard':1},
     'coefficient_payload_bytes':40,'norm_vector_payload_bytes':704,'split_inverse_requested_payload_bytes':1408,
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked field/bit-range and push-order model, source audit and differential tests; not translated Rust/LLVM/SBF.',
     'line_precondition':'Private callback passes its own ordered line vector from the SAME immutable Selected points; arbitrary supplied lines are not equivalent.'}
print(json.dumps(out,indent=2))

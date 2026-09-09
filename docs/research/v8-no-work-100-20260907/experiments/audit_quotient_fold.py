#!/usr/bin/env python3
"""Checked-source algebra, pinned kernels and complete same-proof outcomes."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/quotient-fused'
REV='074daa2fd0636a577f87bb84075e9ad6fd4f5662'
with contextlib.redirect_stdout(io.StringIO()):prior=runpy.run_path(str(EX/'audit_line_norm.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(data):return hashlib.sha256(data).hexdigest()
text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'],cwd=ROOT).decode()
old=[];new=[];active=False
def replace(text,old,new):
    old=''.join(old);new=''.join(new);assert old and text.count(old)==1
    return text.replace(old,new,1)
for line in (EX/'quotient-fused-callback.patch').read_text().splitlines(keepends=True):
    if line.startswith('@@'):
        if active:text=replace(text,old,new)
        old=[];new=[];active=True
    elif active:
        if line[0] in ' -':old.append(line[1:])
        if line[0] in ' +':new.append(line[1:])
assert active
src={**prior['out']['source_sha256'],'relation_callback.rs':sha(replace(text,old,new).encode()),
     'quotient_fold.rs':sha((EX/'quotient_fold.rs').read_bytes())}
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('quotient-fused-max-v1',24);ordinary=evidence('quotient-fused-ordinary-v1',24)
rollback=evidence('quotient-fused-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    prior['prior']['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
resources={}
for job in ('test','selected-test','sbf-build'):
    path=EV/('quotient-fused-'+job+'-v1.log');log=path.read_text()
    resources[job]=prior['prior']['resource'](path)
    if job!='sbf-build':
        assert all(h in log for h in src.values()) and '1 passed; 0 failed' in log
        assert 'arbitrary_profiles=4096 slot_basis_cases=16 zero_challenges_and_coordinates=true' in log
        if job=='selected-test':assert '--cfg v8_qm_channel_partial' in log and '--cfg v8_range_dots' in log
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
log=(EX/'quotient-fold-lean.log').read_text();source=(EX/'QuotientFold.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==4 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/QuotientFold\.olean',log)[-1]
if (EX/'QuotientFold.olean').exists():assert sha((EX/'QuotientFold.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.quotient-fold.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,'resources':resources,'lean':lean,'stack_audit':stack,
     'operation_model':{'old_prepared_qm_products_per_query':3,'new_three_product_sums_per_query':1,
        'additional_alpha_cubing_qm_product':1,'additional_m31_products_per_query':1,
        'additional_m31_halves_per_query':2,'old_qm_halves_per_query':3,'new_qm_halves_per_query':2,
        'old_qm_add_sub_per_query':9,'new_qm_add_sub_per_query':9,
        'new_heap_allocations':0},
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked normalized butterfly identity; reused halving/range kernels, actual-source differential tests and complete controls, not translated Rust/LLVM/SBF.'}
print(json.dumps(out,indent=2))

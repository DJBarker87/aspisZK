#!/usr/bin/env python3
"""Audit delayed compact-boundary reconstruction and complete same-proof costs."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/semantic-boundary'
REV='9d783f0f880dfa263f9a39c90da3093adb86ffe0'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_semantic_carry.py'))
    inversion=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(data):return hashlib.sha256(data).hexdigest()
def source_patch(name,patch):
    text=subprocess.check_output(['git','show',REV+':docs/research/v8-no-work-100-20260907/experiments/'+name],cwd=ROOT).decode()
    old=[];new=[];active=False
    def replace(text,old,new):
        old=''.join(old);new=''.join(new);assert old and text.count(old)==1
        return text.replace(old,new,1)
    for line in (EX/patch).read_text().splitlines(keepends=True):
        if line.startswith('@@'):
            if active:text=replace(text,old,new)
            old=[];new=[];active=True
        elif active:
            if line[0] in ' -':old.append(line[1:])
            if line[0] in ' +':new.append(line[1:])
    assert active
    return sha(replace(text,old,new).encode())
src={**prior['out']['source_sha256'],
     'relation_callback.rs':source_patch('relation_callback.rs','semantic-boundary-callback.patch'),
     'performance_verifier.rs':source_patch('performance_verifier.rs','semantic-boundary-verifier.patch'),
     'semantic_boundary.rs':sha((EX/'semantic_boundary.rs').read_bytes())}
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('semantic-boundary-max-v1',24);ordinary=evidence('semantic-boundary-ordinary-v1',24)
rollback=evidence('semantic-boundary-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    inversion['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
test=(EV/'semantic-boundary-test-v1.log').read_text()
assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
assert 'arbitrary=4096 basis_cells=104 all_maximum_and_zero_edges=true literal_boundary=true' in test
assert '-C overflow-checks=yes' in test
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
log=(EX/'semantic-boundary-lean-v4.log').read_text();source=(EX/'SemanticBoundary.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==8 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/SemanticBoundary\.olean',log)[-1]
if (EX/'SemanticBoundary.olean').exists():assert sha((EX/'SemanticBoundary.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.semantic-boundary.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,
     'resources':{j:inversion['resource'](EV/('semantic-boundary-'+j+'-v1.log')) for j in ('test','sbf-build')},
     'lean':lean,'stack_audit':stack,
     'operation_model':{'semantic_rounds':10,'old_qm31_additions_per_round':28,'old_qm31_subtractions_per_round':1,
        'new_u64_additions_per_round_before_optimisation':4*27,'new_u64_subtractions_per_round':8,
        'new_u64_times_two_per_round':4,'final_m31_reductions_per_round':4,'new_heap_allocations':0},
     'range':{'tail_terms':26,'tail_max':26*(2147483647-1),'pad':28*2147483647,
        'positive_prefix_max':(2147483647-1)+28*2147483647,'word_bound':2**64},
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked literal Nat prefixes, wrapping equivalence, list cast and omitted-coefficient equation over ZMod p. Selected-source differential and complete SBF outcomes, not translated Rust/LLVM/SBF.'}
assert out['range']['positive_prefix_max']<out['range']['word_bound']
print(json.dumps(out,indent=2))

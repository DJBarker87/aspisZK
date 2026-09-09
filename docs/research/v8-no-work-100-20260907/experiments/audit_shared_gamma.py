#!/usr/bin/env python3
"""Audit five shared-weight dots and complete same-proof costs."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/shared-gamma'
REV='081e23f75ae40942234ffd848acf2910d7c929c1'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_semantic_boundary.py'))
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
     'relation_callback.rs':source_patch('relation_callback.rs','shared-gamma-callback.patch'),
     'structured_weights.rs':source_patch('structured_weights.rs','shared-gamma-structured.patch'),
     'shared_gamma.rs':sha((EX/'shared_gamma.rs').read_bytes())}
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('shared-gamma-max-v1',24);ordinary=evidence('shared-gamma-ordinary-v1',24)
rollback=evidence('shared-gamma-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    inversion['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
test=(EV/'shared-gamma-test-v2.log').read_text()
assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
assert 'arbitrary_five_rows=2048 independent_basis=580 canonical_extremes=true gamma_zero_one=true' in test
assert '-C overflow-checks=yes' in test
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
rust=(EX/'shared_gamma.rs').read_text();ref=(EX/'semantic_carry.rs').read_text()
def literal(text):return text[text.index('        let f='):text.index('\n}',text.index('        let f='))].rstrip()
assert literal(rust)==literal(ref)
log=(EX/'shared-gamma-lean-v5.log').read_text();source=(EX/'SharedGammaDots.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==15 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/SharedGammaDots\.olean',log)[-1]
if (EX/'SharedGammaDots.olean').exists():assert sha((EX/'SharedGammaDots.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
refresh=(EX/'shared-gamma-lean-v1.log').read_text()
qsource=sha((EX/'QmCrossRange.lean').read_bytes())
qolean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/QmCrossRange\.olean',log)[-1]
assert qsource=='cb06024066b66778a8e3de356871d4766ce2d6b17a7b698890195f8a9329f409'
assert qsource in refresh and qsource in log and qolean in refresh
qpart=refresh[:refresh.index(qolean)]
assert 'error:' not in qpart and 'sorryAx' not in qpart
if (EX/'QmCrossRange.olean').exists():assert sha((EX/'QmCrossRange.olean').read_bytes())==qolean
refresh_resource={'target':'QmCrossRange.lean','reason':'missing imported olean','stage_exit':0,'combined_log_exit':1,
    'wall_seconds':float(re.search(r'([\d.]+) real',qpart)[1]),
    'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',qpart)[1]),
    'swaps':int(re.search(r'(\d+)  swaps',qpart)[1]),'source_sha256':qsource,'olean_sha256':qolean,
    'log':'experiments/shared-gamma-lean-v1.log'}
assert refresh_resource['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.shared-gamma.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,
     'resources':{'test':inversion['resource'](EV/'shared-gamma-test-v2.log'),'sbf-build':inversion['resource'](EV/'shared-gamma-sbf-build-v1.log')},
     'lean':lean,'dependency_refresh':refresh_resource,'stack_audit':stack,
     'operation_model':{'outputs':5,'old_weight_decompositions':145,'new_weight_decompositions':28,
        'old_value_decompositions':145,'new_value_decompositions':140,'old_products':145,'new_products':140,
        'full_m31_reductions_before_compiler_optimisation_old':5*(8*9+9),'full_m31_reductions_new':20,
        'new_partial_folds':360,'new_heap_allocations':0},
     'range':{'inner_products':4,'inner_max':4*(2147483647-1)**2,
        'outer_chunks':7,'outer_max':4*(2147483647-1)+7*(5*2147483647+3),'word_bound':2**64},
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked canonical limb decomposition, raw product/cast/group recurrence, partial reduction, index grouping, and integer-prefix bounds. Selected-source differential and complete SBF outcomes, not translated Rust/LLVM/SBF.'}
assert max(out['range']['inner_max'],out['range']['outer_max'])<out['range']['word_bound']
print(json.dumps(out,indent=2))

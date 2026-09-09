#!/usr/bin/env python3
"""Audit affine semantic carry, literal reconstruction, and same-proof SBF outcomes."""
import contextlib,hashlib,io,json,re,runpy,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/semantic-carry'
REV='66e39a53215f5bef341e58523230da9dd6adcf8e'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_affine_primal.py'))
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
     'relation_callback.rs':source_patch('relation_callback.rs','semantic-carry-callback.patch'),
     'performance_verifier.rs':source_patch('performance_verifier.rs','semantic-carry-verifier.patch'),
     'semantic_carry.rs':sha((EX/'semantic_carry.rs').read_bytes())}
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
maximum=evidence('semantic-carry-max-v1',24);ordinary=evidence('semantic-carry-ordinary-v1',24)
rollback=evidence('semantic-carry-rollback-v1',2);ms=summary(maximum)
raw=maximum['withdrawal-255-2-success'];artifact=raw['artifacts']['selected_verifier']
for rows,old in ((maximum,base),(ordinary,prior['ordinary']),(rollback,prior['rollback'])):
    inversion['compare'](rows,old,artifact)
    if rows is rollback:assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rows.values())
deltas={s:[a['cu']-b['cu'] for a,b in zip(bs['shapes'][s],xs)] for s,xs in ms['shapes'].items()}
assert all(d>0 for ds in deltas.values() for d in ds)
assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
test=(EV/'semantic-carry-test-v2.log').read_text()
assert all(h in test for h in src.values()) and '1 passed; 0 failed' in test
assert 'arbitrary_affine=4096 degree27_profiles=1024 basis_cases=112 all_four_maximal_prefixes=true selected_reconstruction_raw_cases=4096' in test
assert '--cfg v8_qm_channel_partial' in test and '--cfg v8_range_dots' in test
stack=json.loads((EV/'stack.json').read_text())
assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
# Do not replace the selected integer reconstruction by an assumed black-box identity.
patch='\n'.join(l[1:] for l in (EX/'qm-channel-partial.patch').read_text().splitlines() if l.startswith('+') and not l.startswith('+++'))
rust=(EX/'semantic_carry.rs').read_text()
def literal(text):return text[text.index('        let f='):text.index('    }' if text is patch else '\n}',text.index('        let f='))].rstrip()
assert literal(rust)==literal(patch)
qsource=sha((EX/'QmCrossRange.lean').read_bytes())
assert qsource=='cb06024066b66778a8e3de356871d4766ce2d6b17a7b698890195f8a9329f409'
qlog=(EX/'qm-channel-lean.log').read_text();qextra=(EX/'qm-channel-components-lean.log').read_text()
qrev='32026b0a1dc139f2684dd9dad247901d8d5ecdd2'
for name in ('QmCrossRange.lean','qm-channel-lean.log','qm-channel-components-lean.log'):
    archived=subprocess.check_output(['git','show',qrev+':docs/research/v8-no-work-100-20260907/experiments/'+name],cwd=ROOT)
    assert archived==(EX/name).read_bytes()
assert 'sorryAx' not in qlog+qextra and 'error:' not in qlog
for name in ('raw_partial_range','channel_reconstruction','channel_prefix_ranges','pad32_mod','raw_channel_partial_congr'):
    match=re.search("'AspisV8.QmCross."+name+r"' depends on axioms: \[([^]]*)\]",qlog)
    assert match and set(match[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
log=(EX/'semantic-carry-lean.log').read_text();source=(EX/'SemanticCarry.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==10 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/SemanticCarry\.olean',log)[-1]
if (EX/'SemanticCarry.olean').exists():assert sha((EX/'SemanticCarry.olean').read_bytes())==olean
lean={'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
      'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
      'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
      'swaps':int(re.search(r'(\d+)  swaps',log)[1])}
assert lean['swaps']==0
worst=max(x['cu'] for xs in ms['shapes'].values() for x in xs)
out={'schema':'aspis.research.semantic-carry.v1','base_revision':REV,'selected':True,
     'maximum':ms,'same_proof_savings_cu':deltas,'ordinary':summary(ordinary),'rollback_cases':2,
     'artifacts':{r:raw['artifacts'][r] for r in ('selected_verifier','pool','registry','token_program')},
     'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
     'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
     'excess_over_same_pool_v7':{s:max(x['cu'] for x in xs)-max(x['cu'] for x in bs['shapes'][s])+prior['out']['excess_over_same_pool_v7'][s] for s,xs in ms['shapes'].items()},
     'source_sha256':src,
     'resources':{'test':inversion['resource'](EV/'semantic-carry-test-v2.log'),'sbf-build':inversion['resource'](EV/'semantic-carry-sbf-build-v1.log')},
     'lean':lean,'reused_reconstruction_proof_sha256':qsource,'reused_reconstruction_revision':qrev,'stack_audit':stack,
     'operation_model':{'semantic_rounds':10,'initial_three_product_blocks':10,'carried_four_product_blocks':60,
        'separate_carry_qm31_reconstructions_removed':60,'field_products_added':0,
        'new_heap_allocations':0},
     'range':{'channel_max':4*(2147483647-1)**2+4*(2147483647-1),'word_bound':2**64,'five_products':5*(2147483647-1)**2},
     'actual_peak_allocator_delta_bytes':None,'body_maximum':697*16+52+24+22*621+2*296*26,
     'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,'universal_cu_bound':None,
     'global_security_certificate':None,'prover_time_delta_seconds':None,
     'refinement_status':'Kernel-checked nine-channel product, reconstruction, seeded accumulation/range and Horner recurrence; literal selected reconstruction reused. Source tests and complete outcomes, not translated Rust/LLVM/SBF.'}
assert out['range']['channel_max']<out['range']['word_bound']<out['range']['five_products']
print(json.dumps(out,indent=2))

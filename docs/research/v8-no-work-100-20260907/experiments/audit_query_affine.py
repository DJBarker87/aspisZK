#!/usr/bin/env python3
"""Audit three rejected query-affine lowerings; retain the measured winner."""
import contextlib,hashlib,io,json,re,runpy,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/query-affine'
REV='c3552659714b984fd02b376c2b4e22bebd159c00'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_shared_gamma.py'))
    inv=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(b):return hashlib.sha256(b).hexdigest()
def patched_query():
    path='docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs'
    source=subprocess.check_output(['git','show',REV+':'+path],cwd=ROOT).decode().splitlines(keepends=True)
    patch=(EX/'query-affine-query.patch').read_text().splitlines(keepends=True)
    out=[];pos=0;i=0
    while i<len(patch):
        line=patch[i];i+=1
        m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
        if not m:continue
        old_count=int(m[2] if m[2] is not None else 1)
        new_count=int(m[4] if m[4] is not None else 1)
        start=int(m[1])-(1 if old_count else 0)
        assert pos<=start
        out.extend(source[pos:start]);pos=start;seen_old=seen_new=0
        while i<len(patch) and not patch[i].startswith('@@'):
            tag,text=patch[i][0],patch[i][1:];i+=1
            assert tag in ' +-'
            if tag in ' -':
                assert source[pos]==text
                pos+=1;seen_old+=1
            if tag in ' +':out.append(text);seen_new+=1
        assert (seen_old,seen_new)==(old_count,new_count)
    out.extend(source[pos:])
    return sha(''.join(out).encode())
old_query=sha((EX/'query_affine_arithmetic_v1.rs').read_bytes())
new_query=patched_query()
assert old_query=='7fe8118f97a90682d697aa967860418bc697acb3e5291fec51e93eb638f36e0a'
assert new_query=='1ad3e13d8d84616139c6d15e5868e18279a9a552ba474618247f1303b562f54f'
field='4d9a92f586b63485e1381653a1bc67d54dc20622a467aee4d0da20a571aeefca'
controls={}
for mode,stack_name,kernel,query in [
    ('query-affine','stack-v1.json','query_affine_field_v1.rs',old_query),
    ('query-affine-seeded','stack-seeded-v1.json','query_affine_field.rs',old_query),
    ('query-affine-canonical','stack-canonical-v1.json',None,new_query)]:
    folder=EV/('complete-'+mode+'-max-v1')
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted(folder.glob('*.json'))}
    assert len(rows)==24
    assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    ms=summary(rows);artifact=rows['withdrawal-255-2-success']['artifacts']['selected_verifier']
    inv['compare'](rows,base,artifact)
    for key,x in rows.items():
        for member in ('authenticated_path','atomicity','fixture'):
            assert x[member]==base[key][member],(mode,key,member)
        for member in ('return_data_sha256','return_data_bytes'):
            assert x['execution'][member]==base[key]['execution'][member],(mode,key,member)
    delta={}
    for shape,xs in ms['shapes'].items():
        ref={x['proof_sha256']:x for x in bs['shapes'][shape]}
        delta[shape]=[x['cu']-ref[x['proof_sha256']]['cu'] for x in xs]
    assert all(d>0 for ds in delta.values() for d in ds)
    assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
    test=(EV/(mode+'-test-v1.log')).read_text()
    assert '1 passed; 0 failed' in test and '-C overflow-checks=yes' in test
    assert 'GAMMA_CONTROLS canonical_profiles=512 maximal_limb_dot=true noncanonical_positions=152 short_inputs=2' in test
    src={**prior['out']['source_sha256'],'query_arithmetic.rs':query,'field-overlay.rs':field}
    if kernel:
        src['included-field-kernel.rs']=sha((EX/kernel).read_bytes())
        assert 'QUERY_AFFINE wide_constants=4096 fixed_raw_profiles=1024 maximum_seed=true unchanged_packed_rejections=true' in test
    else:
        assert 'QUERY_AFFINE_CANONICAL selected_existing_helper=true unchanged_packed_rejections=true' in test
    assert all(h in test for h in src.values()),mode
    stack=json.loads((EV/stack_name).read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    controls[mode]={'selected':False,'maximum':ms,'same_proof_delta_cu':delta,
        'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
        'artifact':artifact,'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
        'source_sha256':src,'resources':{job:inv['resource'](EV/(mode+'-'+job+'-v1.log')) for job in ('test','build')},
        'stack_audit':stack,'ordinary':None,'rollback':None,
        'expansion_skipped_reason':'Slower on every maximum-body proof; do not expand rejected performance controls.'}
log=(EX/'query-affine-lean-v4.log').read_text();source=(EX/'QueryAffine.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==15 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/QueryAffine\.olean',log)[-1]
if (EX/'QueryAffine.olean').exists():assert sha((EX/'QueryAffine.olean').read_bytes())==olean
p=2147483647;m=p-1;cap=7*(5*p+3)
assert 3*m*m+4*cap<2**64
out={'schema':'aspis.research.query-affine.v1','base_revision':REV,'controls':controls,
    'selected':'shared-gamma (unchanged)','selected_artifact':prior['out']['artifacts']['selected_verifier'],
    'worst_observed_cu':prior['out']['worst_observed_cu'],'margin_to_1200000':prior['out']['margin_to_1200000'],
    'excess_over_same_pool_v7':prior['out']['excess_over_same_pool_v7'],
    'new_complete_cases':72,'selected_existing_complete_cases':50,
    'range':{'raw_c1_limb_cap':cap,'three_products_plus_wide_seed_max':3*m*m+4*cap,'u64_exclusive':2**64},
    'operation_model':{'slots':88,'wide_variant_removed_full_m31_reductions':352,
        'all_variants_removed_canonical_m31_additions':352,'new_field_products':0,
        'scope':'Literal calls before compiler effects; extra raw offsets, loads/stores and reconstruction remain charged.'},
    'lean':{'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
        'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',log)[1]),
        'log':'experiments/query-affine-lean-v4.log'},
    'body_maximum':697*16+52+24+22*621+2*296*26,
    'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,
    'universal_cu_bound':None,'global_security_certificate':None,
    'prover_time_delta_seconds':None,'new_prover_peak_rss':None,
    'refinement_status':'Kernel-checked raw C1 grouping, cast/reconstruction, literal affine channel injection, seeded order and integer bounds; selected-source differential tests and matched SBF outcomes, not translated Rust/LLVM/SBF.',
    'next_experiment':'Measure moving immutable prepared H/G/D multiplier assembly outside the four-slot query loop; inspect generated copying first, preserve exact canonical/parser checks.'}
assert out['lean']['swaps']==0 and out['body_maximum']==40282
if __name__=='__main__' and sys.argv[1:]==['--check-recorded']:
    # Python integers preserve the u64 bounds exactly; never round-trip this
    # ledger through a binary64-only JSON representation.
    assert out==json.loads((ROOT/'query-affine-results.json').read_text())
    print('Exact recorded ledger matches: 72 complete cases; 15 clean axiom audits.')
else:
    print(json.dumps(out,indent=2))

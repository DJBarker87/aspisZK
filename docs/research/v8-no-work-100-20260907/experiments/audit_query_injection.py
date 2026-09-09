#!/usr/bin/env python3
"""Exact evidence audit: four rejected controls, no selected arithmetic change."""
import contextlib,hashlib,io,json,re,runpy,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments'
REV='a1925696fede0c3b3ca3745ebe0ca4bd8a5a588f'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_shared_gamma.py'))
    inv=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(b):return hashlib.sha256(b).hexdigest()
def patched(name,patch):
    path='docs/research/v8-no-work-100-20260907/experiments/'+name
    source=subprocess.check_output(['git','show',REV+':'+path],cwd=ROOT).decode().splitlines(keepends=True)
    patch=(EX/patch).read_text().splitlines(keepends=True)
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
    out.extend(source[pos:]);return sha(''.join(out).encode())
callback=patched('relation_callback.rs','query-injection-callback.patch')
hoist=patched('query_arithmetic.rs','helper-hoist-query.patch')
assert callback=='ff29f8d7a074dc04b5877505eafb4b55b38d2218a20357d1e744434eabe7b6f9'
assert hoist=='0336ad35e37cae974d009d8db34e1abc75264a1437e1ccd76d76bd7df354bb68'
field='bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0'
query='57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1'
controls={}
for mode,kernel in [
    ('helper-hoist',None),('query-injection','query_injection_generic.rs'),
    ('query-injection-fixed','query_injection_fixed_array.rs'),
    ('query-injection-retained-powers','query_injection.rs')]:
    ev=ROOT/('evidence/helper-hoist' if mode=='helper-hoist' else 'evidence/query-injection')
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((ev/('complete-'+mode+'-max-v1')).glob('*.json'))}
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
    assert all(d==0 if mode=='helper-hoist' else d>0 for ds in delta.values() for d in ds)
    assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
    test=(ev/(mode+'-test-v1.log')).read_text()
    assert '1 passed; 0 failed' in test and '-C overflow-checks=yes' in test
    src={**prior['out']['source_sha256'],'query_arithmetic.rs':query,'field-overlay.rs':field}
    if kernel:
        src['relation_callback.rs']=callback;src['query_injection.rs']=sha((EX/kernel).read_bytes())
        assert 'QUERY_INJECTION arbitrary_profiles=512 complete_weight_tails=32 shape_cases=75 rho_zero_one_max=true shifted_degree_q=true' in test
        if mode!='query-injection':
            assert 'QUERY_INJECTION_FIXED arbitrary_dots=2048 maximum_channels=true six_partial_groups=true' in test
            assert '--cfg v8_query_injection_fixed' in test
    else:
        src['query_arithmetic.rs']=hoist
        assert 'GAMMA_CONTROLS canonical_profiles=512 maximal_limb_dot=true noncanonical_positions=152 short_inputs=2' in test
    assert src['query_arithmetic.rs'] in test and src['relation_callback.rs'] in test and field in test
    if kernel:assert src['query_injection.rs'] in test
    guard=(EX/('check_helper_hoist_sources.sh' if kernel is None else 'check_query_injection_sources.sh')).read_text()
    for h in src.values():assert h in guard or h in (EX/'check_shared_gamma_sources.sh').read_text(),(mode,h)
    stack=json.loads((ev/(mode+'-stack-v1.json')).read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    controls[mode]={'selected':False,'maximum':ms,'same_proof_delta_cu':delta,
        'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
        'artifact':artifact,'elf_delta_bytes':artifact['bytes']-base['withdrawal-255-2-success']['artifacts']['selected_verifier']['bytes'],
        'source_sha256':src,'resources':{job:inv['resource'](ev/(mode+'-'+job+'-v1.log')) for job in ('test','build')},
        'stack_audit':stack,'ordinary':None,'rollback':None,
        'expansion_skipped_reason':'No saving on maximum-body controls; do not expand rejected performance controls.'}
sections=json.loads((ROOT/'evidence/helper-hoist/allocated-sections-v1.json').read_text())
assert sections['reference']['elf_sha256']==prior['out']['artifacts']['selected_verifier']['sha256']
assert sections['candidate']['elf_sha256']==controls['helper-hoist']['artifact']['sha256']
assert not sections['identical_allocated_sections']
log=(EX/'query-injection-lean-v3.log').read_text();source=(EX/'QueryInjection.lean').read_bytes()
assert sha(source) in log and 'error:' not in log and 'sorryAx' not in log
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
zero=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(axs)==19 and len(zero)==2
assert all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/QueryInjection\.olean',log)[-1]
if (EX/'QueryInjection.olean').exists():assert sha((EX/'QueryInjection.olean').read_bytes())==olean
# Literal lowering bridge: the partial-channel reconstruction is byte-identical
# to the previously proved SemanticCarry kernel, not an invented field cast.
def recon(path):
    s=(EX/path).read_text();a=s.index('        let f=|x:u64|');b=s.index('};',s.index('        return QM31',a))+2
    return s[a:b]
assert recon('query_injection.rs')==recon('semantic_carry.rs')
assert recon('query_injection_fixed_array.rs')==recon('semantic_carry.rs')
p=2147483647;m=p-1
assert 4*m*m<2**64 and 6*(5*p+3)<2**64
out={'schema':'aspis.research.query-injection.v1','base_revision':REV,'controls':controls,
    'selected':'shared-gamma (unchanged)','selected_artifact':prior['out']['artifacts']['selected_verifier'],
    'worst_observed_cu':prior['out']['worst_observed_cu'],'margin_to_1200000':prior['out']['margin_to_1200000'],
    'excess_over_same_pool_v7':prior['out']['excess_over_same_pool_v7'],
    'new_complete_cases':96,'selected_existing_complete_cases':50,
    'range':{'four_product_max':4*m*m,'partial_six_group_max':6*(5*p+3),'u64_exclusive':2**64},
    'operation_model':{'queries':22,'emitted_powers':22,'old_updates':22,'seeded_updates':21,
        'generic_dot_groups':[4,4,4,4,4,2],'generic_dot_canonical_channel_reductions':63,
        'fixed_dot_raw_products':198,'fixed_dot_partial_folds':63,'fixed_dot_output_reductions':4,
        'scope':'Literal calls, not metered CU or an end-to-end operation lower bound.'},
    'helper_hoist_allocated_section_comparison':sections,
    'lean':{'source_sha256':sha(source),'olean_sha256':olean,'axioms':{**dict(axs),**{x:'' for x in zero}},'exit':0,
        'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),
        'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',log)[1]),'log':'experiments/query-injection-lean-v3.log'},
    'body_maximum':697*16+52+24+22*621+2*296*26,
    'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,
    'universal_cu_bound':None,'global_security_certificate':None,
    'prover_time_delta_seconds':None,'new_prover_peak_rss':None,
    'refinement_status':'Kernel-checked emitted-power schedule, shifted discrepancy, channel reductions and exact range prefixes; source-shaped differential tests and matched SBF cases, not translated Rust/LLVM/SBF.',
    'next_experiment':'Fuse the four terminal query-weight evaluations, sharing the M31 line factor and preserving deferred halvings; compare against all four weight_at values before combining the carried image coefficient.'}
assert out['lean']['swaps']==0 and out['body_maximum']==40282
if __name__=='__main__' and sys.argv[1:]==['--check-recorded']:
    assert out==json.loads((ROOT/'query-injection-results.json').read_text())
    print('Exact recorded ledger matches: 96 complete cases; 21 clean axiom audits.')
else:print(json.dumps(out,indent=2))

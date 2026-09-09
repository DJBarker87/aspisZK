#!/usr/bin/env python3
"""Audit terminal fusion, source overlays, axiom scope and matched complete CU."""
import contextlib,hashlib,io,json,re,runpy,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent;EX=ROOT/'experiments';EV=ROOT/'evidence/terminal-query'
REV='04e2d26e9b7b169e95fe11d0d62d4225b8c9b795'
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(EX/'audit_shared_gamma.py'))
    inv=runpy.run_path(str(EX/'audit_inversion_fusion.py'))
check,summary=prior['check'],prior['summary'];base=prior['maximum'];bs=summary(base)
def sha(b):return hashlib.sha256(b).hexdigest()
def patched(path,patch):
    source=subprocess.check_output(['git','show',REV+':'+path],cwd=ROOT).decode().splitlines(keepends=True)
    patch=(EX/patch).read_text().splitlines(keepends=True)
    out=[];pos=0;i=0
    while i<len(patch):
        line=patch[i];i+=1
        m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',line)
        if not m:continue
        old_count=int(m[2] if m[2] is not None else 1);new_count=int(m[4] if m[4] is not None else 1)
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
ep='docs/research/v8-no-work-100-20260907/experiments/'
structured=patched(ep+'structured_weights.rs','terminal-query-structured.patch')
semantic=patched(ep+'performance_verifier.rs','terminal-query-semantic-stack.patch')
sumcheck=patched('crates/aspis-core/src/sumcheck.rs','terminal-query-sumcheck.patch')
test_callback=patched(ep+'relation_callback.rs','terminal-query-host-test.patch')
assert test_callback=='3c49fd8ccb5654dbe1067fbb5d923eec472fdff1e5303a558b778a53302d87a9'
assert structured=='06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089'
assert semantic=='cdccf89cba145831138e6ac93272e262e6e377f9ea9835058d0ceb38701d8c6e'
assert sumcheck=='c89f1df5cc4928e852bedeb886f9179998b1cbb12c603b280e26dddaef61e72a'
def evidence(folder,n):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((EV/folder).glob('*.json'))}
    assert len(rows)==n and all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    return rows
def compare(rows,old,artifact):
    inv['compare'](rows,old,artifact)
    for key,x in rows.items():
        for m in ('authenticated_path','atomicity','fixture'):assert x[m]==old[key][m],(key,m)
        for m in ('return_data_sha256','return_data_bytes'):assert x['execution'][m]==old[key]['execution'][m],(key,m)
def delta(ms,ref):
    out={}
    for shape,xs in ms['shapes'].items():
        byid={x['proof_sha256']:x['cu'] for x in ref['shapes'][shape]}
        out[shape]=[x['cu']-byid[x['proof_sha256']] for x in xs]
    return out
controls={};allrows={}
baseline_diagnostics=re.findall(r'^Error:.*$',(ROOT/'evidence/shared-gamma/shared-gamma-sbf-build-v1.log').read_text(),re.M)
assert len(baseline_diagnostics)==12 and len(set(baseline_diagnostics))==1
assert 'performance_verifier8semantic' in baseline_diagnostics[0] and 'overwrites values in the frame' in baseline_diagnostics[0]
for mode,kernel in [('terminal-prefix','terminal_query_prefix.rs'),('terminal-fixed','terminal_query_fixed.rs'),('terminal-fused','terminal_query.rs'),('terminal-stack','terminal_query.rs')]:
    rows=evidence('complete-'+mode+'-max-v1',24);allrows[mode]=rows
    ms=summary(rows);artifact=rows['withdrawal-255-2-success']['artifacts']['selected_verifier']
    compare(rows,base,artifact);ds=delta(ms,bs)
    assert all(d<0 for xs in ds.values() for d in xs)
    assert all(x['body']==40282 for xs in ms['shapes'].values() for x in xs)
    src={**prior['out']['source_sha256'],
        'structured_weights.rs':sha((EX/'terminal_query_structured_v1.rs').read_bytes()) if mode in ('terminal-prefix','terminal-fixed') else structured,
        'terminal_query.rs':sha((EX/kernel).read_bytes()),
        'sumcheck.rs':'7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead' if mode=='terminal-prefix' else sumcheck,
        'field-overlay.rs':'bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0',
        'query_arithmetic.rs':'57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1'}
    if mode=='terminal-stack':src['performance_verifier.rs']=semantic
    guard=(EX/'check_terminal_query_sources.sh').read_text()
    assert all(h in guard for h in src.values())
    testpath=EV/(mode+('-test-v3.log' if mode=='terminal-stack' else '-test-v1.log'))
    log=testpath.read_text()
    assert '-C overflow-checks=yes' in log
    if mode=='terminal-stack':
        assert '1 passed; 0 failed' in log
        assert '--cfg v8_payment_extraction --cfg v8_performance --cfg v8_performance_fast' in log
        assert 'TERMINAL_QUERY arbitrary_batches=1024 four_outputs=true shifted_scales_unchanged=true image_included=true' in log
        assert 'TERMINAL_QUERY_SHAPES cases=45 empty_dense_tensor_multi=true halvings_0_to_8=true prefix3_fallback=true' in log
        assert 'TERMINAL_IMAGE_FUSION arbitrary_scalars=1024 canonical_extremes=3 checked=true' in log
    else:
        # Initial runner compiled but omitted the enclosing host module. These
        # are failed test-discovery preflights, never successful unit gates.
        assert 'running 0 tests' in log and '0 passed; 0 failed' in log
    assert all(h in log for k,h in src.items() if k not in ('query_arithmetic.rs','performance_verifier.rs','relation_callback.rs'))
    assert (test_callback if mode=='terminal-stack' else src['relation_callback.rs']) in log
    assert src['performance_verifier.rs'] in log
    build=(EV/(mode+'-build-v1.log')).read_text()
    diagnostics=re.findall(r'^Error:.*$',build,re.M)
    if mode=='terminal-stack':assert not diagnostics and '--cfg v8_semantic_stack' in build
    else:assert diagnostics==baseline_diagnostics
    stack=json.loads((EV/(mode+'-stack-v1.json')).read_text())
    assert stack['max_direct_frame_offset']<=4096 and not stack['unused_warning_function_emitted']
    controls[mode]={'selected':mode=='terminal-stack','maximum':ms,'same_proof_delta_cu':ds,
        'artifact':artifact,'source_sha256':src,
        'worst_observed_cu':max(x['cu'] for xs in ms['shapes'].values() for x in xs),
        'resources':{'test':inv['resource'](testpath) if mode=='terminal-stack' else None,
            'failed_test_discovery_preflight':inv['resource'](testpath) if mode!='terminal-stack' else None,
            'build':inv['resource'](EV/(mode+'-build-v1.log'))},
        'compiler_frame_diagnostics':diagnostics,'direct_frame_scan':stack}
maximum=allrows['terminal-stack'];ms=summary(maximum);artifact=controls['terminal-stack']['artifact']
ordinary=evidence('complete-terminal-stack-ordinary-v1',24);rollback=evidence('complete-terminal-stack-rollback-v1',2)
for rows,ref in [(ordinary,prior['ordinary']),(rollback,prior['rollback'])]:compare(rows,ref,artifact)
assert all(x['execution']['selected_verifier_cpi_observed_in_logs'] for x in rollback.values())
v7={s:max(x['cu'] for x in xs)-prior['out']['excess_over_same_pool_v7'][s] for s,xs in bs['shapes'].items()}
vs_v7={s:max(x['cu'] for x in xs)-v7[s] for s,xs in ms['shapes'].items()}
assert all(d<0 for d in vs_v7.values())
log=(EX/'terminal-query-lean-v4.log').read_text();source=(EX/'TerminalQuery.lean').read_bytes()
assert sha(source) in log and not re.search(r'error:|sorryAx',log)
assert not re.search(rb'\b(sorry|axiom)\b',source)
axs=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(axs)==15 and all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in axs)
olean=re.findall(r'([a-f0-9]{64})\s+[^\n]+/TerminalQuery\.olean',log)[-1]
if (EX/'TerminalQuery.olean').exists():assert sha((EX/'TerminalQuery.olean').read_bytes())==olean
worst=controls['terminal-stack']['worst_observed_cu']
out={'schema':'aspis.research.terminal-query.v1','base_revision':REV,'selected':'terminal-stack','controls':controls,
    'maximum':ms,'ordinary':summary(ordinary),'rollback_cases':2,'new_complete_cases':122,
    'worst_observed_cu':worst,'margin_to_1200000':1200000-worst,
    'same_pool_v7_maxima':v7,'excess_over_same_pool_v7':vs_v7,
    'intermediate_same_proof_delta_cu':{b:delta(controls[b]['maximum'],controls[a]['maximum']) for a,b in [('terminal-prefix','terminal-fixed'),('terminal-fixed','terminal-fused'),('terminal-fused','terminal-stack')]},
    'artifacts':{k:maximum['withdrawal-255-2-success']['artifacts'][k] for k in ('selected_verifier','pool','registry','token_program')},
    'source_sha256':controls['terminal-stack']['source_sha256'],
    'host_test_only_callback_sha256':test_callback,
    'test_discovery_correction':{'initial_omitted_enclosing_module':True,
        'second_attempt_compile_exit':101,'second_attempt_reason':'Imported prover test modules require crate::HOST_HASH.',
        'second_attempt_log':'evidence/terminal-query/terminal-stack-test-v2.log',
        'final_test_only_patch':'experiments/terminal-query-host-test.patch',
        'no_sbf_or_transcript_change':True},
    'operation_model':{'query_count':22,'terminal_outputs':4,'old_line_index_walks':88,'new_line_index_walks':22,
        'source_double_x_calls_old':176,'generic_prefix_double_x_calls':44,'fixed_prefix_double_x_calls':22,
        'mixed_multiplications_old':88,'mixed_multiplications_new':66,'deferred_qm31_halvings':24,
        'old_final_qm31_products':5,'new_final_qm31_products':4,
        'scope':'Literal source calls, before dead-code elimination; not a CU estimate.'},
    'lean':{'source_sha256':sha(source),'olean_sha256':olean,'axioms':dict(axs),'exit':0,
        'wall_seconds':float(re.search(r'([\d.]+) real',log)[1]),'rss_bytes':int(re.search(r'(\d+)  maximum resident set size',log)[1]),
        'swaps':int(re.search(r'(\d+)  swaps',log)[1]),'log':'experiments/terminal-query-lean-v4.log'},
    'body_maximum':697*16+52+24+22*621+2*296*26,'new_proof_or_transcript_bytes':0,'grinding_credit_bits':0,
    'universal_cu_bound':None,'global_security_certificate':None,'actual_peak_allocator_delta_bytes':None,
    'prover_time_delta_seconds':None,'new_prover_peak_rss':None,
    'refinement_status':'Kernel-checked low-bit traversal, shared component sums, deferred-halving interface, image-in-terminal identity and raw four-product/range interface; actual Rust/SBF differential and complete tests, not translated Rust/LLVM/SBF.',
    'next_experiment':'Bound accepted full-transaction CU over the actual selected traversal and challenge-sampling grammar; first isolate unbounded-by-body retry work from fixed-cost folds/authentication. Keep average/matched fixtures distinct from that bound.'}
assert out['lean']['swaps']==0 and out['body_maximum']==40282
if __name__=='__main__' and sys.argv[1:]==['--check-recorded']:
    assert out==json.loads((ROOT/'terminal-query-results.json').read_text())
    print('Exact ledger matches: 122 complete cases; 15 clean axiom audits; four measured V7 shape maxima beaten.')
else:print(json.dumps(out,indent=2))

#!/usr/bin/env python3
"""Audit the new source/basis/zip results without rerunning unchanged Lean."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
ev=area/'evidence/cu-equivalence-20261019';start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-rho-basis.py','extract-rho-accumulate.py']:
    subprocess.run([sys.executable,str(here/script),'--check'],check=True,capture_output=True)
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1RhoBasis'/name).read_bytes()==(here/'rho-basis-generated'/name).read_bytes()
targets={
    'CuSavingsRhoInputs':'rho-inputs-c','CuSavingsLoopInvariant':'rho-loop-invariant-a',
    'AspisR1RhoBasis/Types':'rho-basis-types-a','AspisR1RhoBasis/FunsExternal':'rho-basis-externals-a',
    'AspisR1RhoBasis/Funs':'rho-basis-funs-a','CuSavingsRhoBasis':'rho-basis-proof-b',
    'CuSavingsZipLoans':'rho-zip-loans-b','CuSavingsZipFill':'rho-zip-fill-b',
    'CuSavingsRhoZipInitialization':'rho-zip-initialization-b','CuSavingsRhoBasisPipeline':'rho-basis-pipeline-a'}
objects={};results={};receipts={}
for module,attempt in targets.items():
    path=ev/attempt/'receipt.json';r=json.loads(path.read_text());receipts[module]=r
    assert r['exit_status']==0
    source=area/'lean'/(module+'.lean');assert sha(source.read_bytes())==r['source_sha256']==sha((ev/attempt/'source.lean').read_bytes())
    log=(ev/attempt/'stdout.log').read_text();assert log==r['print_axioms_output']
    assert 'sorryAx' not in log and 'error:' not in log
    declarations=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert declarations
    for name,axioms in declarations:
        assert set(filter(None,axioms.replace(' ','').split(','))) <= {'propext','Classical.choice','Quot.sound'},name
    objects[module.replace('/','.')]=r['object_sha256']
    results[module]=dict(attempt=attempt,source_sha256=r['source_sha256'],receipt_sha256=sha(path.read_bytes()),
        declarations=[n for n,_ in declarations],exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],
        process_swaps=r['process_swaps'],cgroup_swap_bytes=r['cgroup_swap_bytes'])
for module,r in receipts.items():
    for item in r['direct_imports']:
        if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
original_modules=['CuSavingsZipLoans','CuSavingsZipFill','CuSavingsRhoZipInitialization','CuSavingsRhoBasisPipeline']
for module in original_modules:
    cache=receipts[module]['cache_provenance']
    assert cache['priority']=='NEW_CU_MODULES_THEN_EXACT_ORIGINAL_CLOSURE'
    assert cache['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
diagnostics={}
for attempt in ['rho-charon-init-transparent-a','rho-aeneas-init-transparent-a','rho-charon-init-mono-a',
                'rho-basis-charon-a','rho-basis-aeneas-a']:
    p=ev/attempt/'receipt.json';r=json.loads(p.read_text())
    diagnostics[attempt]=dict(receipt_sha256=sha(p.read_bytes()),exit=r['exit_status'],wall_seconds=r['wall_seconds'],
        peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],sampled_aggregate_peak_bytes=r['peak_aggregate_rss_bytes_sampled'],
        cgroup_memory_peak_bytes=r['cgroup_memory_peak_bytes'],cgroup_swap_current=r['cgroup_swap_current'])
assert diagnostics['rho-charon-init-mono-a']['exit']==-15
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_BASIS_AND_RUNTIME_ZIP_COMPONENTS_CHECKED_FULL_CALLER_OPEN',candidate_complete=False,
    source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
    production_revision='39c2971dd16c95858a4cfd2c9ae35da052eacfa9',
    successes=results,source_diagnostics=diagnostics,
    zip_runtime_boundary='Existing original-cache generic Zip.next and mutable SliceIter.next. Loan packaging and fill composition are proved using those definitions. This is a runtime component proof, not an automatically emitted full BatchedWeights::new body.',
    basis_source_boundary='Complete exact common Rust prefix, with stable a.weights.len() made a scalar input; inverse substitution checked. Raw generated Types/Funs promoted bytes-unchanged, existing M31 methods bound directly.',
    remaining=['Full BatchedWeights::new source wrapper and sufficient-resource allocation binding',
        'Actual accumulate/query source context, source power/length invariants and counter handoff',
        'Actual tx1_finish/tx2/tx2_authenticated, checkpoint/oracle/effect composition'],
    stopped_run_metrics_note='SIGTERM stopped the entire timed process group. Final GNU-time process RSS/swap are unavailable; sampled aggregate peak, cgroup memory peak and observed zero cgroup swap are retained. No exact process peak is invented.',
    audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
        print_axioms='N/A: source/receipt audit only; individual focused Lean results above'))
(ev/'RHO-SOURCE-INVARIANTS.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

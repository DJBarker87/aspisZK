#!/usr/bin/env python3
"""Check source normalization, focused receipts and inherited cache coherence."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
ev=area/'evidence/cu-equivalence-20261019';start=time.monotonic()
sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['extract-rho-init-wrapper.py','emit-rho-init-wrapper.py','extract-rho-heap.py','emit-rho-heap.py']:
    subprocess.run([sys.executable,str(here/name),'--check'],check=True,capture_output=True)
# Compare the entire emitted wrapper body with the interpreted source wrapper.
# The ONLY substitution is the proved original-runtime for-loop interpretation.
emitted=(area/'lean/AspisR1RhoInit/Funs.lean').read_text().split('def verifier.BatchedWeights.new\n')[1].split(':= do',1)[1].split('\nend AspisR1CuRho')[0]
source=(area/'lean/CuSavingsRhoInitSource.lean').read_text().split('def sourceNew ')[1].split(':= do',1)[1].split('\ntheorem source_eq')[0]
norm=lambda s:re.sub(r'\s+','',s).replace('.ok(', 'ok(')
assert norm(emitted.replace('verifier.initialize_weights','sourceFor'))==norm(source)
# The assignment interpreted in the zip proof must be the exact extracted RHS.
loop=(here/'rho-init-wrapper-input/fragments/for.rs').read_text() if (here/'rho-init-wrapper-input/fragments/for.rs').exists() else None
if loop is None:
    fragments=list((here/'rho-init-wrapper-input/fragments').glob('*'))
    loop=next(p.read_text() for p in fragments if p.read_text().lstrip().startswith('for (out,w)'))
assert '*out=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];' in loop
results={};receipts={};objects={}
targets={
'AspisR1RhoInit/Types':'rho-init-wrapper-types-b',
'AspisR1RhoInit/FunsExternal':'rho-init-wrapper-externals-c',
'AspisR1RhoInit/Funs':'rho-init-wrapper-funs-b',
'CuSavingsRhoInitSource':'rho-init-source-c',
'AspisR1RhoHeap/TypesExternal':'rho-heap-types-external-a',
'AspisR1RhoHeap/Types':'rho-heap-types-b',
'AspisR1RhoHeap/FunsExternal':'rho-heap-externals-a',
'AspisR1RhoHeap/Funs':'rho-heap-funs-a',
'CuSavingsRhoHeap':'rho-heap-proof-b',
'CuSavingsRhoAllocationBound':'rho-allocation-bound-c'}
for module,attempt in targets.items():
    receipt=ev/attempt/'receipt.json';r=json.loads(receipt.read_text());receipts[module]=r
    assert r['exit_status']==0
    assert sha((area/'lean'/(module+'.lean')).read_bytes())==r['source_sha256']==sha((ev/attempt/'source.lean').read_bytes())
    log=(ev/attempt/'stdout.log').read_text();assert log==r['print_axioms_output']
    assert 'sorryAx' not in log and 'error:' not in log
    decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert decls
    for name,axioms in decls:
        assert set(filter(None,axioms.replace(' ','').split(','))) <= {'propext','Classical.choice','Quot.sound'},name
    objects[module.replace('/','.')]=r['object_sha256']
    cache=r['cache_provenance']
    if cache:
        assert cache['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
    else:
        assert module=='CuSavingsRhoAllocationBound'
        assert r['direct_imports']==[dict(module='Aeneas',path='/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend/.lake/build/lib/lean/Aeneas.olean',sha256='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d')]
    results[module]=dict(attempt=attempt,source_sha256=r['source_sha256'],receipt_sha256=sha(receipt.read_bytes()),
        declarations=[name for name,_ in decls],command=r['command'],revision=r['source_revision'],features=r['features'],
        exit=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],
        cgroup_swap_bytes=r['cgroup_swap_bytes'])
for module,r in receipts.items():
    for item in r['direct_imports']:
        if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='WHOLE_INITIALIZER_OUTCOME_CHECKED_RESOURCE_AND_CALLER_COMPOSITION_OPEN',candidate_complete=False,
    source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,
    source_binding='Exact inverse-inlined Rust helper factoring plus equality to the complete emitted wrapper. Original Vec/slice/Zip handbacks interpreted and proved equal; sourceNew full body compared here with the emitted wrapper up to that single replacement.',
    heap_binding='Whole actual heap::filled emitted after declaration-only rename. Every successful result length follows from original Vec.resize for arbitrary reserve behavior. No reserve success/frame or initializer length premise in initializer_outcome.',
    resource_boundary='Actual pinned SDK bump arithmetic bounds checked symbolically: extra Raw4 storage at most 8199 bytes for 256 rows, 2055 for 64 rows. Source reserve/SDK link and common caller future-resource budget remain open; this is not a full sufficient-resources theorem.',
    remaining=['Source reserve/SDK sufficient-resource binding and caller budget','Actual accumulate/query traversal, caller power/length/counter invariants','Actual tx1_finish/tx2/tx2_authenticated and observable-context composition'],
    rejected_native_attempt='rho-allocation-bound-a: Lean exited 0 but native bv_decide axioms were rejected. Superseded by symbolic rho-allocation-bound-c.',
    audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
        print_axioms='N/A source/receipt audit; focused Lean audits listed above'))
(ev/'RHO-INITIALIZER.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

#!/usr/bin/env python3
"""Audit the checked source reference traversal and its consuming batch bridge."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
ev=area/'evidence/cu-equivalence-20261019';start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest()
checks=['extract-rho-accumulate.py','extract-rho-coefficients.py','extract-rho-diagnostics.py','emit-rho-diagnostics.py','emit-rho-reference-loop.py']
for name in checks:subprocess.run([sys.executable,str(here/name),'--check'],check=True,capture_output=True)
targets={
'CuSavingsRangeTraversal':'rho-range-traversal-b',
'AspisR1RhoDiagnostics/Types':'rho-diagnostics-types-b',
'AspisR1RhoDiagnostics/Funs':'rho-diagnostics-funs-a',
'CuSavingsRhoDiagnostics':'rho-diagnostics-proof-c',
'AspisR1RhoReferenceLoop/Types':'rho-reference-loop-types-a',
'AspisR1RhoReferenceLoop/FunsExternal':'rho-reference-loop-externals-a',
'AspisR1RhoReferenceLoop/Funs':'rho-reference-loop-funs-a',
'CuSavingsRhoReferenceLoop':'rho-reference-loop-proof-f',
'CuSavingsRhoRangeInputs':'rho-range-inputs-b',
'CuSavingsRhoReferenceTraversal':'rho-reference-traversal-c',
'CuSavingsRhoSourceBatch':'rho-source-batch-b'}
objects={};receipts={};results={}
for module,attempt in targets.items():
 path=ev/attempt/'receipt.json';r=json.loads(path.read_text());receipts[module]=r
 assert r['exit_status']==0
 assert sha((area/'lean'/(module+'.lean')).read_bytes())==r['source_sha256']==sha((ev/attempt/'source.lean').read_bytes())
 log=(ev/attempt/'stdout.log').read_text();assert log==r['print_axioms_output']
 assert 'error:' not in log and 'sorryAx' not in log
 decls=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert decls
 for name,axioms in decls:assert set(filter(None,axioms.replace(' ','').split(','))) <= {'propext','Classical.choice','Quot.sound'},name
 cache=r['cache_provenance'];assert cache['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256']
 results[module]=dict(attempt=attempt,source_sha256=r['source_sha256'],receipt_sha256=sha(path.read_bytes()),
  command=r['command'],source_revision=r['source_revision'],features=r['features'],exit=0,
  wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],
  cgroup_swap_bytes=r['cgroup_swap_bytes'],declarations=[n for n,_ in decls])
for module,r in receipts.items():
 for item in r['direct_imports']:
  if item['module'] in objects:assert item['sha256']==objects[item['module']],(module,item['module'])
for folder in ['AspisR1RhoDiagnostics','AspisR1RhoReferenceLoop']:
 for path in (area/'lean'/folder).glob('*.lean'):
  assert not re.search(r'(?m)^axiom\s',path.read_text()),path
# The consuming statement must name the complete source function and actual basis.
bridge=(area/'lean/CuSavingsRhoSourceBatch.lean').read_text()
assert 'AspisR1RhoCoefficients.rho_old.coefficients (canonicalSlice self)' in bridge
assert 'AspisR1RhoBasis.basis (alloc.vec.Vec.len (canonicalSlice self))' in bridge
assert 'CuSavingsRhoReferenceTraversal.source_eq' in bridge
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='COMPLETE_REFERENCE_COEFFICIENT_SOURCE_TRAVERSAL_AND_BATCH_BRIDGE_CHECKED_CANDIDATE_OPEN',candidate_complete=False,
 source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
 source_checks=checks,successes=results,
 covered=['Exact source diagnostic constructors are total for arbitrary raw words; non-prover trace calls are no-ops.',
 'Both executed source diagnostic indices are checked and fit under next<=22, rows<=256 and source-loop bounds.',
 'The original Range iterator traverses the exact rho index/basis items with unique full coverage.',
 'Complete emitted old coefficient loop equals referenceUpdates, preserving arithmetic failures/divergence without a canonicality or callback-totality premise.',
 'The consuming source_batch theorem compares that full source function with the checked optimized batch; its basis admission follows from the actual emitted basis result.'],
 explicit_remaining_premises=['Caller next<=22 and actual weights length<=256','Canonical power and pending Good/count invariant derived from actual enclosing callers','Successful basis result is the actual common-prefix execution; whole accumulate field-projection context still needs composition'],
 remaining=['Optimized coefficient-loop Option reborrow source binding (no replacement template axiom admitted)',
 'Actual accumulator suffix and tx1_finish/tx2/tx2_authenticated composition, including source canonicality/length/counter invariants',
 'Reserve/SDK sufficient-resource source binding and complete future-resource budget',
 'Final checkpoint, ordered cryptographic calls and settlement effects theorem'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,
 peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,
 print_axioms='N/A source/receipt audit; focused Lean #print axioms listed above'))
(ev/'RHO-REFERENCE-TRAVERSAL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

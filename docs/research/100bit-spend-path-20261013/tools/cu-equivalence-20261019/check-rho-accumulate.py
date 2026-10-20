#!/usr/bin/env python3
"""Audit the complete factored source contexts and their whole-result proof."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for n in ['extract-rho-accumulate-factored.py','emit-rho-accumulate.py']:
 subprocess.run([sys.executable,str(tool/n),'--check'],check=True,capture_output=True)
# Verify the already checked coefficient bridge without replaying Lean.
subprocess.run([sys.executable,str(tool/'check-rho-optimized-traversal.py')],check=True,capture_output=True)
targets={'AspisR1RhoAccumulate/Types':'rho-accumulate-types-a','AspisR1RhoAccumulate/FunsExternal':'rho-accumulate-externals-a','AspisR1RhoAccumulate/Funs':'rho-accumulate-funs-a','CuSavingsRhoAccumulate':'rho-accumulate-proof-e'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 path=ev/attempt/'receipt.json';r=json.loads(path.read_text());assert r['exit_status']==0
 src=(area/'lean'/(module+'.lean')).read_bytes();assert sha(src)==r['source_sha256'];assert src==(ev/attempt/'source.lean').read_bytes()
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 ds=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert ds
 for n,a in ds:assert set(filter(None,re.sub(r'\s+','',a).split(',')))<={'propext','Classical.choice','Quot.sound'},(n,a)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(path.read_bytes()))
for module,r in receipts.items():
 for i in r['direct_imports']:
  if i['module'] in objects:assert i['sha256']==objects[i['module']],(module,i)
raw=(tool/'rho-accumulate-factored-generated/Funs.lean').read_text();assert 'fail panic' not in raw
bindings=(area/'lean/AspisR1RhoAccumulate/FunsExternal.lean').read_text();assert not re.search(r'(?m)^axiom\b',bindings)
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
source={}
for attempt in ['rho-accumulate-factored-charon-b','rho-accumulate-factored-aeneas-b']:
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0;source[attempt]={k:r[k] for k in ['source_revision','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps']};source[attempt]['receipt_sha256']=sha(p.read_bytes())
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='WHOLE_SOURCE_ACCUMULATION_OUTCOME_EQUIVALENCE_AND_INVARIANT_PRESERVATION_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,source_extractions=source,
 source_binding=['Complete original old/new accumulate_with_node bodies from exact parent/candidate, inverse-checked factoring of their complete basis and coefficient blocks only.',
 'Entire emitted caller function bodies are unchanged. Only an implicit computational common-RHS parameter is added at namespace level; identical fields/BatchedWeights/variant use audited carrier aliases.',
 'Both basis calls bind the actual emitted basis function, both coefficient calls bind the complete checked source traversals, power multiplication binds the actual current source, and trace is the exact non-prover source.',
 'Unchanged WideExact RHS multiply/add remain arbitrary shared computations with no propositional law or equivalence premise. The theorem holds for every such common computation, including failure/divergence.'],
 proved=['Whole source old accumulation equals the new source accumulation followed by the actual source final materializer, under explicit local input invariants. Basis failure/divergence, RHS failure/divergence, power failure/divergence, and counter overflow are included; no child-success premise.',
 'A successful whole new source call derives Good raw bounds, incremented pending terms, preserved raw length/stale weights, canonical updated power, and next+1 <=22, from the local pre-state invariant and canonical rho. No child-call canonicality or success premise.'],
 remaining=['Derive starting invariants from actual initialization/resume and allocation resource behavior.','Compose actual query/stage loops and tx1_finish/tx2/tx2_authenticated contexts.','Complete checkpoint/hash-order/settlement observational transfer; candidate 12 is not yet closed.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A receipt audit; exact per-target audits included'))
(ev/'RHO-ACCUMULATE.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

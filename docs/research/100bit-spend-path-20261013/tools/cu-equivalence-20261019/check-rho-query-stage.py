#!/usr/bin/env python3
"""Audit actual source query and stage outcome proofs."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
for script in ['extract-rho-query-context.py','extract-rho-stage-context.py','emit-rho-query.py','emit-rho-stage.py']:
 subprocess.run([sys.executable,str(tool/script),'--check'],check=True,capture_output=True)
targets={'AspisR1RhoQuery/Types':'rho-query-types-b','AspisR1RhoQuery/FunsExternal':'rho-query-externals-e','AspisR1RhoQuery/Funs':'rho-query-funs-c','CuSavingsRhoQuery':'rho-query-proof-g','AspisR1RhoStage/Types':'rho-stage-types-b','AspisR1RhoStage/FunsExternal':'rho-stage-externals-c','AspisR1RhoStage/Funs':'rho-stage-funs-b','CuSavingsRhoStage':'rho-stage-proof-e'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 src=(area/'lean'/(module+'.lean')).read_bytes();assert sha(src)==r['source_sha256'];assert src==(ev/attempt/'source.lean').read_bytes()
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 ds=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert ds
 for n,a in ds:assert set(filter(None,re.sub(r'\s+','',a).split(',')))<={'propext','Classical.choice','Quot.sound'},(n,a)
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(p.read_bytes()))
for module,r in receipts.items():
 for i in r['direct_imports']:
  if i['module'] in objects:assert i['sha256']==objects[i['module']],(module,i)
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_QUERY_AND_TRANSACTION_STAGE_OUTCOME_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,
 proved=['Source old/new node selection agrees on every variant, including outer errors/divergence. No domain-node property assumed.',
 'Whole owned query contexts preserve rejection and divergence and materialize the same accumulator. They consume the checked whole accumulation theorem.',
 'Successful whole optimized query derives the next Good/canonical/counter/length invariant. No assumed child-success premise.',
 'Actual emitted stage while loops agree under symbolic remaining-query induction, retaining query rejection, failures and divergence. No concrete 22-query normalization.',
 'Whole source stage outcome is exactly the old stage preceded by the extra whole source initializer. Thus all initializer errors are retained explicitly; no allocation success is assumed.',
 'Source pins cover the exact tx1_finish, tx2 and tx2_authenticated stage blocks, which are identical modulo their end bound.'],
 source_boundaries=['Exact common query prefix is pinned once and parametrized as an arbitrary identical computation. It receives the same index and no mutable accumulator/pending argument.',
 'Old node branch uses exact wrapper-node inlining and distributes its identical accumulation continuation. The source node theorem checks all variants. Prefix inverse substitution and untouched query suffix are checked.',
 'Owned query API exposes the private accumulator/pending local handbacks. Rust rejection occurs in the common prefix before mutation; source stage query adapters preserve those unchanged rejection handbacks.',
 'No raw Aeneas external templates are admitted. Identical nominal carriers are aliased, with explicit init-error constructor transport. Unused unqualified discriminant registrations are omitted to avoid duplicate imported instance names; enum constructors/order are unchanged.'],
 remaining=['Compose actual preparation and resume entry-state bindings plus complete transaction suffix observables.','Discharge extra allocation success from explicit source heap/resources. Source stage theorem currently exposes allocation outcomes rather than claiming unconditional OOM equivalence.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A receipt audit; per-target lists included'))
(ev/'RHO-QUERY-STAGE.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

#!/usr/bin/env python3
"""Audit concrete source specialization, whole traversals, and consuming bridge."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
started=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019'
sha=lambda b:hashlib.sha256(b).hexdigest()
for name in ['extract-rho-coefficients.py','emit-rho-optimized-loop.py']:
 subprocess.run([sys.executable,str(tool/name),'--check'],check=True,capture_output=True)
kit=tool/'rho-source-option-input';pins=json.loads((kit/'source-pins.json').read_text())
for n,h in pins['files'].items():assert sha((kit/n).read_bytes())==h
raw=tool/'rho-source-option-generated';assert (raw/'Funs.lean').read_bytes()==(area/'lean/AspisR1RhoSourceOption/Funs.lean').read_bytes()
# The only emitted datatype transport is the exact raw/terms record alias.
types=(raw/'Types.lean').read_text();assert '«raw» : alloc.vec.Vec (Array Std.U64 4#usize)\n  terms : Std.Usize' in types
assert 'axiom ' not in (area/'lean/AspisR1RhoOptimizedLoop/FunsExternal.lean').read_text()
targets={'AspisR1RhoSourceOption/Types':'rho-source-option-types-b','AspisR1RhoSourceOption/Funs':'rho-source-option-funs-a','CuSavingsRhoSourceOption':'rho-source-option-proof-c','AspisR1RhoOptimizedLoop/FunsExternal':'rho-optimized-loop-externals-a','AspisR1RhoOptimizedLoop/Funs':'rho-optimized-loop-funs-a','CuSavingsRhoOptimizedTraversal':'rho-optimized-traversal-h','CuSavingsRhoSourceBatch':'rho-source-both-a'}
results={};objects={};receipts={}
for module,attempt in targets.items():
 path=ev/attempt/'receipt.json';r=json.loads(path.read_text());assert r['exit_status']==0
 assert sha((area/'lean'/(module+'.lean')).read_bytes())==r['source_sha256'];assert (area/'lean'/(module+'.lean')).read_bytes()==(ev/attempt/'source.lean').read_bytes()
 log=r['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 ds=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log);assert ds
 for name,axs in ds:assert set(filter(None,re.sub(r'\s+','',axs).split(',')))<={'propext','Classical.choice','Quot.sound'}
 assert r['cache_provenance']['selected_owner_objects']['Aeneas']['sha256']=='d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'
 objects[module.replace('/','.')]=r['object_sha256'];receipts[module]=r
 results[module]={k:r[k] for k in ['source_revision','source_sha256','object_sha256','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps','cgroup_swap_bytes','print_axioms_output']};results[module].update(attempt=attempt,receipt_sha256=sha(path.read_bytes()))
for module,r in receipts.items():
 for i in r['direct_imports']:
  if i['module'] in objects:assert i['sha256']==objects[i['module']],(module,i)
source_runs={}
for attempt in ['rho-source-option-charon-a','rho-source-option-aeneas-b','rho-option-branch-repair-a']:
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 source_runs[attempt]={k:r[k] for k in ['source_revision','features','command','exit_status','wall_seconds','peak_rss_kib','process_swaps']};source_runs[attempt]['receipt_sha256']=sha(p.read_bytes())
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
u=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_OPTIMIZED_COEFFICIENT_TRAVERSAL_AND_REFERENCE_MATERIALIZATION_CHECKED',candidate_complete=False,source_revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),successes=results,source_extractions=source_runs,
 source_specialization=['One opaque generic method instance is replaced with a complete emitted single-call wrapper of that exact concrete Rust std method. The wrapper uses the original .as_deref_mut() expression; no branch-normalized surrogate or compatible hand-written API is substituted.',
 'Raw wrapper Funs is byte-unchanged. Its raw/terms datatype is transported to the identical existing BatchedWeights carrier.',
 'Both original new coefficient loop bodies and term increment are selected from the original emission. Only the exact concrete callee specialization changes; inverse replacement restores the raw declarations byte-for-byte.',
 'All push, field, constructor, and diagnostic boundaries bind checked source or the original runtime. No opaque template axioms.'],
 producer_repair=['Pinned upstream b59d5188 source archive from the existing native tool build, two source changes only. Full baseline file hashes and patch retained.',
 'Optimized MIR mutable Copy is handled by fresh borrow/loan reborrowing, never duplicating a mutable borrow ID.',
 'Given-back translation skips ancestor loan projectors only when current_level differs from abs_level; original error checks remain for relevant-level and active borrow projectors.',
 'Strict -checks remains enabled. Explicit rustc Inline/ForceInline enables actual std dependency inlining despite Charon resetting mir_opt_level to zero.'],
 proved=['Whole source helper, both writebacks, Some/None outcomes.',
 'Whole optimized coefficient traversal equals the checked batch, preserving errors/divergence of push and counter overflow under explicit diagnostic index bounds.',
 'Consuming source_both compares actual optimized and reference coefficient loops and actual final materialization under the existing local arithmetic invariants.'],
 remaining=['Actual caller invariants and query/transaction context composition.','Actual reserve frame/sufficient-resource connection and resumed-weight canonicality.','Full tx1_finish, tx2, tx2_authenticated outcomes/checkpoints/hash order/settlement theorem.'],
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-started,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,process_swaps=u.ru_nswap,print_axioms='N/A receipt audit; per-target audits included'))
(ev/'RHO-OPTIMIZED-TRAVERSAL.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

#!/usr/bin/env python3
"""Record the source-admission blocker without admitting a compatible model."""
from pathlib import Path
import hashlib,json,re,resource,subprocess,sys,time
start=time.monotonic();here=Path(__file__).resolve().parent;repo=here.parents[4];area=here.parents[1];ev=area/'evidence/cu-equivalence-20261019';sha=lambda b:hashlib.sha256(b).hexdigest()
revision=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
raw=(here/'rho-coefficients-generated/Funs.lean').read_text();template=(here/'rho-coefficients-generated/FunsExternal_Template.lean').read_text()
assert 'let (o1, as_deref_mut_back, as_deref_mut_back1) ←' in raw
sig=template.split('axiom core.option.Option.as_deref_mut',1)[1].split('/--',1)[0]
assert 'Result ((Option Clause0_Clause0_Target) × (Option' in sig
assert 'Clause0_Clause0_Target → Option T))' in sig
assert 'Binding this packaging to the original nested-borrow caller is a' in (area/'lean/CuSavingsRhoOptionLoans.lean').read_text()
# The current accepted tree must not already contain an admitted optimized
# coefficient caller that this report would incorrectly claim is absent.
accepted_new=[]
for p in (area/'lean').rglob('*.lean'):
 if 'rho_new.coefficients' in p.read_text():accepted_new.append(str(p.relative_to(repo)))
assert not accepted_new,accepted_new
checks={}
for report in ['RHO-INITIALIZER.json','RHO-REFERENCE-TRAVERSAL.json','RHO-ACCUMULATOR-NEW.json','RHO-PREPARED.json','RHO-OPTION-LOANS.json']:
 p=ev/report;j=json.loads(p.read_text());assert j['candidate_complete'] is False
 checks[report]=dict(status=j['status'],sha256=sha(p.read_bytes()),candidate_complete=False)
# Revalidate the actual focused predecessors used to establish the current
# frontier. Read their receipts/source; do not repeat unchanged Lean jobs.
predecessors={}
for module,attempt in [('CuSavingsRhoHeap','rho-heap-proof-b'),('CuSavingsRhoSourceBatch','rho-source-batch-a'),('CuSavingsRhoOptionLoans','rho-option-loans-proof-c'),('CuSavingsRhoAccumulatorNew','rho-accumulator-new-proof-c'),('CuSavingsRhoPrepared','rho-prepared-proof-d'),('CuSavingsRhoInitialPower','rho-initial-power-proof-a')]:
 p=ev/attempt/'receipt.json'
 if not p.exists() or json.loads(p.read_text()).get('exit_status')!=0 or json.loads(p.read_text()).get('source_sha256')!=sha((area/'lean'/(module+'.lean')).read_bytes()):
  # Locate an exact current successful receipt for the named target rather
  # than guessing a differently named historical attempt.
  matches=[]
  for q in ev.glob('*/receipt.json'):
   r=json.loads(q.read_text())
   if r.get('module')==module and r.get('exit_status')==0 and r.get('source_sha256')==sha((area/'lean'/(module+'.lean')).read_bytes()):matches.append(q)
  assert matches,module;p=matches[-1]
 r=json.loads(p.read_text());assert r['exit_status']==0
 assert r['source_sha256']==sha((area/'lean'/(module+'.lean')).read_bytes())
 assert 'sorryAx' not in r['print_axioms_output'] and 'error:' not in r['print_axioms_output']
 predecessors[module]=dict(attempt=p.parent.name,source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],receipt_sha256=sha(p.read_bytes()))
# Exact latest source-only concrete specialization attempt: no accepted Lean
# artifact is inferred from its successful Charon translation.
kit=here/'rho-concrete-option-input';pins=json.loads((kit/'source-pins.json').read_text())
for n,pin in pins['kit_files'].items():assert sha((kit/n).read_bytes())==pin
assert (here/'rho-local-option-input/lib.rs').read_bytes() in (kit/'lib.rs').read_bytes()
assert (here/'rho-input/fragments/batched_weights.rs').read_bytes() in (kit/'lib.rs').read_bytes()
diagnostics={}
for attempt,exit_expected in [('rho-concrete-option-charon-a',0),('rho-concrete-option-aeneas-a',2),('rho-resume-weights-aeneas-a',2),('rho-resume-weights-aeneas-b',2)]:
 p=ev/attempt/'receipt.json';r=json.loads(p.read_text());assert r['exit_status']==exit_expected
 diagnostics[attempt]=dict(receipt_sha256=sha(p.read_bytes()),command=r['command'],source_revision=r['source_revision'],features=r['features'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],process_swaps=r['process_swaps'],print_axioms='N/A: source extraction only, no Lean result')
assert 'llbc/TypesAnalysis.ml, line 229' in (ev/'rho-concrete-option-aeneas-a/stderr.log').read_text()
assert subprocess.check_output(['git','-C',str(repo),'diff','39c2971dd16c95858a4cfd2c9ae35da052eacfa9','--','crates','programs'])==b''
usage=resource.getrusage(resource.RUSAGE_SELF)
report=dict(status='SOURCE_ADMISSION_BLOCKED_NO_WHOLE_CANDIDATE_PROOF',candidate_complete=False,source_revision=revision,accepted_frontier=checks,checked_predecessors=predecessors,source_diagnostics=diagnostics,
 requirements=[dict(id=1,status='PARTIAL',evidence='RHO-INITIALIZER.json',open='Actual reserve frame/source SDK link and sufficient-resource caller budget.'),dict(id=2,status='PARTIAL_SOURCE_ADMISSION_BLOCKED',evidence=['RHO-REFERENCE-TRAVERSAL.json','RHO-ACCUMULATOR-NEW.json','RHO-PREPARED.json'],open='Original optimized coefficient loop nested-reference API lowering and complete actual query/caller composition.'),dict(id=3,status='NOT_PROVED',evidence='No accepted optimized coefficient source definition is present in the Lean tree.',open='Actual tx1_finish, tx2 and tx2_authenticated full outcome/checkpoint/hash-order/settlement equivalence.'),dict(id=4,status='FOCUSED_PREDECESSORS_CHECKED_FULL_CLOSURE_OPEN',evidence='Per-target source/object/command/axioms/resource receipts; no whole-candidate theorem/closure receipt.'),dict(id=5,status='SATISFIED_FOR_CURRENT_CHECKPOINT',evidence='Production Rust matches frozen revision; side-branch commits only; no compiled binary artifacts intended for commit.')],
 exact_blocker='Raw optimized loop expects three Option reborrow outputs; original emitted external declaration provides two. Transparent original-source, local exact-source, concrete full-monomorphized source and actual-owned resume loop attempts are rejected by the pinned producer. No triple-result source lowering has been established.',
 rejected_shortcut='Instantiating generic non-borrowed as_mut/map leaf models with erased pointee values does not prove the required nested-borrow instantiation/lifetime/writeback correspondence. Defining a compatible triple-return adapter would leave an additional unproved source-lowering premise. It is not admitted.',
 blocked_audit='This same unsupported source borrow-lowering condition persisted through at least the last three goal work turns (5c76ce633, 5fa4ec2d5, 832d394a1/2e7a701af and this audit). Independent initialization/preparation scalar/counter predecessors are now checked. Additional compatible-model/component lemmas cannot establish the missing source admission. Completing the mandatory source-consuming root requires producer/runtime support or a changed proof-target scope.',
 required_scope_decision='Permit proof-producer/runtime support work for the exact Option<&mut BatchedWeights> reborrow and original resume mutable-iterator/Reader patterns, with original production Rust kept frozen; otherwise retain this proof as incomplete and blocked.',
 audit=dict(command=[sys.executable,str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,process_swaps=usage.ru_nswap,print_axioms='N/A current-state/receipt audit; checked Lean predecessors listed above'))
(ev/'RHO-SOURCE-BINDING-BLOCKER.json').write_text(json.dumps(report,indent=2)+'\n');print(report['status'])

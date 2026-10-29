"""Report only receipt-backed results; canonical candidates retain caller links."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028/resume16');R=D/'receipts'
rows=json.loads((R/'run-index.json').read_text());by={r['harness']:r for r in rows};passed=lambda n:by.get(n,{}).get('status')=='PASS'
x=json.loads((D/'CLASSIFY.json').read_text());models={r['function']:r for r in json.loads(Path('evidence/pv-b3p6-20261028/resume15/link-status.json').read_text())}
composed={};composition={
 'reconstruct_10':('equivalence16::reconstruct_10','PV_B3P_Binding13227.reconstruct_link13'),
 'equality_value':('equivalence16::equality_value','PV_B3P_Binding13227.equality_link13'),
 'sum_high':('equivalence16::sum_high_actual_calls','PV_B3P_Binding13227.sum_high_link13'),
 'add_digest_binding':('equivalence16::add_digest_binding','PV_B3P_Binding13227.digeststore_link13')}
for name,(h,l)in composition.items():
 if passed(h):composed[name]=dict(native_gate=by[h]['run'],reference_link=l,domain='full fixed-array field inputs' if name in ['reconstruct_10','equality_value']else 'caller domain discharged in DOMAINS.json',modulo_callees='SHARED-CALLEES.json'if name=='equality_value'else None)
maskruns=[by.get('equivalence16::selector_mask_host_'+str(m),{})for m in [1749,2048,2049,4097,6144,6145,26214]]
if all(r.get('status')=='PASS'for r in maskruns)and passed('equivalence16::selector_domain'):
 composed['selector_mask_sum_16']=dict(native_gates=[r['run']for r in maskruns],reference_link='PV_B3P_Correct14227.mask_direct14 / native_mask_link14',domain='seven nonzero masks; sole caller and all frozen table cells checked; total u16 equality not claimed')
# Shared abstract-callee credit needs both controls, not just a named stub.
if 'equality_value'in composed and not(passed('equivalence16::shared_repeat16')and by.get('equivalence16::shared_wrong16',{}).get('exit')==1):del composed['equality_value']
for f in x['functions']:
 name=f['function'];h='remaining_equivalence16::'+name if 'remaining_'in f['harness_source']else 'equivalence16::'+name
 if name=='sum_high':h='equivalence16::sum_high_actual_calls'
 f['native_result']=by.get(h,{}).get('status','UNRUN')
 f['native_receipt']=by.get(h,{}).get('receipt')
 f['reference_link']=models[name].get('model_theorem')or models[name].get('resume15_model_theorem')
 if name in composed:
  f['native_result']='PASS';f['equivalence']='PASS, admissible deployed caller domain';f['composed_binding']='RECLASSIFIED under owner fifth amendment';f['composition']=composed[name]
 else:
  f['composed_binding']='OPEN';f['equivalence']=f['native_result']
  if f['native_result']=='PASS'and name in ['add_preweighted','external_linear_lazy','external_local_packed_raw','external_linear_packed','internal_linear_lazy']:f['equivalence']='PASS on canonical domain ONLY; caller canonicality link OPEN'
  if name=='at_point':f['native_result']='UNRUN known-refuted legacy draft; corrected 57-block context remains OPEN'
x['results']=dict(changed_functions=36,reclassified=len(composed),open=36-len(composed),model_contexts=sum(f['model_context']for f in x['functions']),reclassification_label='reclassification within existing Charon/Aeneas tool trust (owner fifth amendment); Kani P6 tool trust',baseline_reachable=79,baseline_bound=41,now_bound=41+len(composed),now_reclassification_bound=40+len(composed),own1_bound=1,exact_reachability_uncertified=True,endpoint_premises_removed=0,trust_fields_added=0,runjoin_op227_discharged=False,lean_attempts=0,kani_scopes=len(rows),other_native_scopes=0,direct_trials=0)
(D/'CLASSIFY.json').write_text(json.dumps(x,indent=2)+'\n')
lines=['# D511 resume16 per-function status','', '**V244 remains OPEN. Target not yet established.** No endpoint premise removed; V370 / D381,D386, T, simulator and observer unchanged.','',f"Changed-function associations: **{len(composed)}/36 reclassified**, {36-len(composed)} OPEN. Model/context instances remain 23/36. Historical inventory: 79 conservative reachable candidates; {41+len(composed)} BOUND = {40+len(composed)} reclassification + 1 own-1. No reachability pruning. The statement-copy mask gate is ancillary to this denominator.",'','These are admissible-domain source/reference + reference-link associations under owner fifth amendment and P6 tool trust, not removal or a composed privacy proof. Fresh direct-extraction acceptance/refusal remains UNKNOWN for all 36 (no dedicated extractor scope allocated).','', '| Function | Route | Native evidence | Composition / residual |','|---|---|---|---|']
for f in x['functions']:
 detail='RECLASSIFIED; '+str(f['composition']['reference_link'])if f['function']in composed else 'OPEN; '+f['equivalence']
 if f['function']=='at_point':detail='OPEN; legacy49 direct draft retained as refuted; corrected layout57 context not verified'
 lines.append(f"| {f['function']} | ({f['route']}) provisional; direct unknown | {f['native_result']} | {detail} |")
lines+=['','Canonical-only PASS gates retain **PV_B3P_Link_callers_canonical16** as an explicit OPEN obligation. Every crate grep site is in CLASSIFY.json; DOMAINS.json distinguishes discharged static caller checks from this unproved invariant. No generality is dropped silently.','', 'Source harnesses are type-checked, not all verified. The legacy constructor draft is not a positive candidate. Unrun gates and timeouts earn no credit. Shared callees are bound by their immutable extraction chains in SHARED-CALLEES.json. Existing Lean reference proofs/audits are reused; no unchanged full replay was launched.']
(D/'GROUP-STATUS.md').write_text('\n'.join(lines)+'\n')
# Correct stale entry revision labels by exact committed source hash matching;
# never mutate the original receipts.
revs=subprocess.check_output(['git','rev-list','95febdf539..HEAD'],text=True).splitlines();reconciled=[]
for r in rows:
 matches={}
 for name in ['equivalence16.rs','lib_leaf16.rs','host_terminal_kani16.rs','reference_terminal_kani16.rs']:
  path='tools/pv-b3p6-20261028/v244/'+name;want=r.get('source_hashes',{}).get(path)
  if not want:continue
  for rev in reversed(revs):
   z=subprocess.run(['git','show',rev+':'+path],capture_output=True)
   if z.returncode==0 and hashlib.sha256(z.stdout).hexdigest()==want:matches[path]=rev;break
 reconciled.append(dict(run=r['run'],recorded_revision=r['source_revision'],exact_committed_source_matches=matches,note='Original receipt retained; early runner revision label was stale. Hashes, not labels, select the exact input. Unmatched intermediate files are not given an invented source revision.'))
(D/'source-revision-reconciliation.json').write_text(json.dumps(reconciled,indent=2)+'\n')
(D/'verification-summary.json').write_text(json.dumps(dict(results=x['results'],runs=rows,admission_check='every charged receipt admission and in-scope barrier allowed:true; exact caps checked by collector',unchanged_shipped_sources=subprocess.run(['git','diff','--quiet','95febdf539','--','crates','programs']).returncode==0,new_lean_axioms='N/A; no Lean source changes or new theorem. Reused source links retain resume13/resume14/resume15 standard-axiom audits.',source_revision_corrections='source-revision-reconciliation.json',canonical_only_results_not_promoted=True,all_direct_extraction_refusals=None),indent=2)+'\n')
print(json.dumps(x['results']))

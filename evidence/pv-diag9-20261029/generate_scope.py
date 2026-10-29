from pathlib import Path
import json
D=Path(__file__).parent;m='PV_DIAG9_Scope'
s='''import PV_DIAG9_Honest
import PV_DIAG9_Retry
import R1Z.ProverRwRetryModel
set_option autoImplicit false
noncomputable section
namespace PV_DIAG9
open Aeneas Aeneas.Std Result R1Z
'''
steps=[('map_result_panic_reflection','''theorem map_result_panic_reflection {A B : Type} (f : A → B) (r : Result A)
 (h : ProverCommitSemanticTransport26.mapR f r ≠ .fail .panic) : r ≠ .fail .panic := by
 intro hr; apply h; rw [hr]; rfl'''),
('extracted_retry_no_panic','''theorem extracted_retry_no_panic [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
 {C : Type} (entropy : ProverRwRetryModel.Entropy C)
 (pub : ProverRwRetryModel.Pub) (compiled : ProverRwRetryModel.Compiled)
 (variant : ProverRwFull.transport.Variant) (hash : ProverRwRetryModel.Hash)
 (store : ProverRwRetryModel.Store) (callback : C)
 (k : Usize) (n : Nat) (bound : k.val+n=8)
 (attemptLaw : ∀ index state, ∃ out,
  ProverRwRetryModel.attempt entropy pub compiled variant hash index state=.ok out) :
 ProverRwFull.prover.retry_attempt entropy pub compiled variant hash store callback k ≠ .fail .panic := by
 apply map_result_panic_reflection ProverRwRetryModel.sourceOutput
 rw [ProverRwRetryModel.retry entropy pub compiled variant hash store callback k n bound]
 obtain ⟨out,ho⟩ := retry_terminates (ProverRwRetryModel.attempt entropy pub compiled variant hash)
  attemptLaw n k.val (callback,store)
 rw [ho]
 exact ok_excludes_panic rfl'''),
('caught_panic_can_return_normally','''/-- A counterexample to transferring wrapper success across a panic-catching
boundary; this is the control shape of catch_unwind, not a native leak. -/
theorem caught_panic_can_return_normally :
 let caught := fun r : Result Bool => match r with
  | .ok b => .ok b
  | .fail _ => .ok false
  | .div => .div
 caught (.fail .panic)=.ok false := rfl'''),
('honest_compiler_no_rust_error','''theorem honest_compiler_no_rust_error
 {K : Type} [Field K] [Fintype K] [DecidableEq K]
 [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
 (i : PV_RunJoin_HonestIdentification26.Honest (K := K))
 (e : BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceErrorV1) :
 @PV_Src_NativeInput.run PV_RunJoin_ShippedExternal.E_shipped
  PV_RunJoin_UniversalRecords22.shipped i.val ≠ .ok (.Err e) := by
 rw [PV_RunJoin_HonestIdentification26.success i]
 intro h; cases h''')]
steps=steps[:2]
cs=[]
for n,d in steps:s+=d+'\n#print axioms '+n+'\n';cs.append(s+'end PV_DIAG9\n')
j=json.loads((D/'plans.json').read_text());j[m]=cs;(D/'plans.json').write_text(json.dumps(j,indent=2)+'\n');(D/(m+'.lean')).write_text(cs[-1])

import NGM_FinishControl
import NGM_FinishDomain
import NHE_Round
import NHE_DotDeployed
set_option autoImplicit false
noncomputable section
namespace NHQ_FinishRelationModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeFinishBody NGM_FinishControl
variable {W : Type}

def staged (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) : Result (R Unit) := do
 let alpha0 ← Array.index_usize p.alpha 0#usize
 bindChild (ops.op5 v.round0 alpha0 p.claim 0#usize) fun claim0 => do
  let folds ← ops.op6 p.variant
  if folds = 2#usize then
   let alpha1 ← Array.index_usize p.alpha 1#usize
   bindChild (ops.op5 v.round1 alpha1 claim0 1#usize)
    (afterClaim ops v p a obs folds)
  else afterClaim ops v p a obs folds claim0

/-- Stage boundaries retain errors, divergence, order and SAME returned values. -/
theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs = staged ops v p a obs := by
 simp only [Port3_NativeFinishBody.verifier.finish_relation,staged,bindChild,
  afterClaim,afterPair,afterDot]
 congr 12

/-- The pair law's required interface is the full Result on the SAME W/alpha/message/kappa.
It is not a premise that pair succeeds or equals claim. -/
theorem pair_stage (ops : Ops W) (v : verifier.View) (a : verifier.Accumulator)
 (obs : Option (verifier.Phase → Result Unit)) (claim : E)
 (weights : W) (alpha : Slice E) (kappa : E) (packet : Result (R E))
 (NHM_pair : ops.op2 weights alpha v.final_message kappa = packet) :
 bindChild (ops.op2 weights alpha v.final_message kappa) (afterPair ops v a obs claim) =
 bindChild packet (afterPair ops v a obs claim) := by rw [NHM_pair]

theorem child_error {A B : Type} (error : verifier.Error) (next : A → Result (R B)) :
 bindChild (ok (.Err error)) next = ok (.Err error) := by rfl

theorem child_fail {A B : Type} (error : Aeneas.Std.Error) (next : A → Result (R B)) :
 bindChild (.fail error) next = .fail error := by rfl

theorem child_div {A B : Type} (next : A → Result (R B)) :
 bindChild .div next = .div := by rfl

#print axioms source
#print axioms pair_stage
#print axioms child_error
#print axioms child_fail
#print axioms child_div
end NHQ_FinishRelationModel

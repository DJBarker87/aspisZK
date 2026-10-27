import R1Z.PDict_Compare
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Abort
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

abbrev installed := PDict_Compare.selected

theorem wire_retained (ops : ExternalFuns) :
    (installed ops).op256 = PDict_WireError.equal := rfl

theorem semantic_error (ops : ExternalFuns) (e : r1_wire.Error) :
    @prover.semantic_error _ (installed ops) e =
      .ok (match e with
        | .ActivePole => verifier.Error.Rejected
        | _ => verifier.Error.Semantic) := by
  unfold prover.semantic_error
  change (do
    let b ← (installed ops).op256 e .ActivePole
    if b then .ok verifier.Error.Rejected else .ok verifier.Error.Semantic) = _
  rw [wire_retained]
  cases e <;> rfl

/-- Keeps the actual P_R1 call and both outer machine failures; no assumption
about that checker or its returned decision is required. -/
theorem public_check (ops : ExternalFuns) (v : transport.Variant)
    (ch : aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges)
    (root : Array U8 32#usize) :
    @prover.public_check _ (installed ops) v ch root =
      (match v with
       | .S2 => do
         let (accepted,_) ← (installed ops).op232 ch
         if accepted then .ok (.Ok ()) else .ok (.Err verifier.Error.Rejected)
       | _ => .ok (.Err verifier.Error.Semantic)) := by
  cases v <;> rfl

#print axioms wire_retained
#print axioms semantic_error
#print axioms public_check
end R1Z.PDict_Abort

import NP6_StdModel

/-! Complete Result normalization for the owned safe reference. Native P6
and dictionary installation are separate obligations, not hypotheses hidden
inside this normalization. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsModel
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent
open NP6_StdModel

def normalized (reservation : Reservation) (prefix : r1_wire.Prefix) : Result Status := do
  let record ← (ClaimsUnrolledFinish.external (calls reservation)).validated prefix 25#u8
  match record with
  | .Err e => ok (.Err e)
  | .Ok vr =>
    match reservation with
    | .Err _ => ok (.Err .Allocation)
    | .Ok () => decodeRows (ClaimsUnrolledFinish.external (calls reservation)) vr

theorem filled_contents (reservation : Reservation) {T : Type}
    (copy : core.marker.Copy T) (n : Usize) (value : T) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls reservation)) copy n value =
      match reservation with
      | .Err _ => ok (.Err .Allocation)
      | .Ok () => ok (.Ok (⟨List.replicate n.val value, by simp; scalar_tac⟩ : alloc.vec.Vec T)) := by
  cases reservation with
  | Err e => rfl
  | Ok u =>
    cases u
    simp only [aspis_core.r0.heap.filled, ClaimsUnrolledFinish.external, calls,
      alloc.vec.Vec.new, mapError, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    simp [alloc.vec.Vec.resize, List.resize]

theorem reference_normalized (reservation : Reservation) (prefix : r1_wire.Prefix) :
    claimsReference (ClaimsUnrolledFinish.external (calls reservation)) prefix =
      normalized reservation prefix := by
  unfold claimsReference normalized
  cases h : (ClaimsUnrolledFinish.external (calls reservation)).validated prefix 25#u8 with
  | fail e => simp [h]
  | div => simp [h]
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok vr =>
      cases reservation with
      | Err e =>
        simp [h, zero, filled_contents, mapError,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]
      | Ok u =>
        cases u
        simp [h, zero, filled_contents, mapError, ClaimsUnrolledFinish.external,
          calls, alloc.vec.Vec.deref, boxArray,
          core.result.Result.Insts.CoreOpsTry.branch]

#print axioms filled_contents
#print axioms reference_normalized
end AspisR1.NP6_ClaimsModel
end

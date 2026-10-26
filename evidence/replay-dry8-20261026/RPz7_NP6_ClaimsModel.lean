import RPz7_NP6_StdModel
/-! Complete Result normalization for the owned safe reference. Native P6
and dictionary installation are separate obligations, not hypotheses hidden
inside this normalization. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NP6_ClaimsModel
open Aeneas Aeneas.Std Result
open AspisR1ClaimsUnrolledParent
open NP6_StdModel

def normalized (reservation : Reservation) (pre : r1_wire.Prefix) : Result Status := do
  let record ← (ClaimsUnrolledFinish.external (calls reservation)).validated pre 25#u8
  match record with
  | .Err e => ok (.Err e)
  | .Ok vr =>
    match reservation with
    | .Err _ => ok (.Err .Allocation)
    | .Ok () => decodeRows (ClaimsUnrolledFinish.external (calls reservation)) vr

theorem filled_contents (reservation : Reservation) {T : Type}
    (copy : core.marker.Copy T) (n : Usize) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) :
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
    simp [alloc.vec.Vec.resize, List.resize, cloned]

theorem row_clone (row : Row) :
    (Array.Insts.CoreMarkerCopy 29#usize aspis_core.field.QM31.Insts.CoreMarkerCopy).cloneInst.clone row = ok row := by
  obtain ⟨out,returned,same⟩ := WP.spec_imp_exists
    (Array.clone_spec (s := row) (clone := aspis_core.field.QM31.Insts.CoreCloneClone.clone)
      (by intro x hx; rfl))
  subst out
  exact returned

theorem row_filled (reservation : Reservation) (n : Usize) (row : Row) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls reservation))
      (Array.Insts.CoreMarkerCopy 29#usize aspis_core.field.QM31.Insts.CoreMarkerCopy) n row =
      match reservation with
      | .Err _ => ok (.Err .Allocation)
      | .Ok () => ok (.Ok (⟨List.replicate n.val row, by simp; scalar_tac⟩ : alloc.vec.Vec Row)) :=
  filled_contents reservation _ n row (row_clone row)

theorem reference_normalized (reservation : Reservation) (pre : r1_wire.Prefix) :
    claimsReference (ClaimsUnrolledFinish.external (calls reservation)) pre =
      normalized reservation pre := by
  unfold claimsReference normalized
  cases h : (ClaimsUnrolledFinish.external (calls reservation)).validated pre 25#u8 with
  | fail e => simp [h]
  | div => simp [h]
  | ok r =>
    cases r with
    | Err e => rfl
    | Ok vr =>
      cases reservation with
      | Err e =>
        simp [h, zero, row_filled, mapError,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          candidate_claims.claims.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once]
      | Ok u =>
        cases u
        simp only [zero, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
        rw [row_filled]
        simp [mapError, ClaimsUnrolledFinish.external,
          calls, alloc.vec.Vec.deref, boxArray,
          core.result.Result.Insts.CoreOpsTry.branch]

#print axioms filled_contents
#print axioms row_clone
#print axioms row_filled
#print axioms reference_normalized
end AspisR1.NP6_ClaimsModel
end

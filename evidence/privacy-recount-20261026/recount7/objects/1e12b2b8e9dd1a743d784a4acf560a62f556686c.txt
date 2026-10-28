import R1Z.PV_B2_C_ConstructorRow4
set_option autoImplicit false
noncomputable section
namespace PV_B2_C_ConstructorCompose
open Aeneas Aeneas.Std Result
open PV_B2_C_ArrayTotal PV_B2_C_WeightsNative PV_B2_C_ConstructorRows

/-- Exact constructor factored at five fixed factor-row boundaries. -/
def factored (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let points ← host_weights.state_only_statement_points alpha
  let q ← Array.index_usize alpha 8#usize
  let q1 ← Array.index_usize alpha 9#usize
  let factors := Array.repeat 5#usize (Array.repeat 5#usize
    (Array.repeat 4#usize aspis_core.field.QM31.ZERO))
  let factors ← row0 factors points
  let factors ← row1 factors points
  let factors ← row2 factors points
  let factors ← row3 factors z
  let factors ← row4 factors z
  ok (.Ok {variant,factors,points,extra := Array.make 2#usize [q,q1]})

theorem factored_total (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : RustOk (factored variant alpha z) := by
  unfold factored
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.points alpha)
  intro points
  apply bind_rust _ _ (read _ _ (by decide))
  intro q
  apply bind_rust _ _ (read _ _ (by decide))
  intro q1
  apply bind_rust _ _ (row0_total _ points)
  intro factors
  apply bind_rust _ _ (row1_total _ points)
  intro factors
  apply bind_rust _ _ (row2_total _ points)
  intro factors
  apply bind_rust _ _ (row3_total _ z)
  intro factors
  apply bind_rust _ _ (row4_total _ z)
  intro factors
  exact ⟨_,rfl⟩

#print axioms factored_total
end PV_B2_C_ConstructorCompose

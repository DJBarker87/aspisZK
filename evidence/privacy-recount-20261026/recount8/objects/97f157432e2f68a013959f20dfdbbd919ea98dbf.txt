import R1Z.PV_RDB2C_PV_B2_C_MutationTotal
set_option autoImplicit false
namespace PV_B2_C_MaterializeWrapper
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- The complete mutable caller return includes both Rust status and updated storage. -/
theorem result (w : host_weights.Weights) (k : E) (out : Out) :
    pv_b2_materialize w k out = (do
      let updated ← host_weights.materialize_values w k out
      ok (core.result.Result.Ok (),updated)) := by rfl

theorem error (w : host_weights.Weights) (k : E) (out : Out) (e : Error)
    (he : host_weights.materialize_values w k out = fail e) :
    pv_b2_materialize w k out = fail e := by
  rw [result,he,bind_tc_fail]

theorem divergence (w : host_weights.Weights) (k : E) (out : Out)
    (he : host_weights.materialize_values w k out = div) :
    pv_b2_materialize w k out = div := by
  rw [result,he,bind_tc_div]

/-- Conditional composition, keeping powers/cell totality as explicit P obligations. -/
theorem total (w : host_weights.Weights) (kappa : E) (out : Out)
    (k : Powers) (hp : host_weights.powers7 kappa = ok k)
    (hc : PV_B2_C_MutationTotal.CellsTotal w k) :
    ∃ updated, pv_b2_materialize w kappa out = ok (core.result.Result.Ok (),updated) := by
  obtain ⟨updated,he⟩ := PV_B2_C_MutationTotal.loop_total w k hc out 0#usize
  refine ⟨updated,?_⟩
  rw [result]
  simp only [host_weights.materialize_values,hp,bind_tc_ok,he]
#print axioms result
#print axioms error
#print axioms divergence
#print axioms total
end PV_B2_C_MaterializeWrapper

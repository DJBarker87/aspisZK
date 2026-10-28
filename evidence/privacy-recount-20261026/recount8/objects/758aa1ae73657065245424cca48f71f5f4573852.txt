import R1Z.PV_RDB2C_PV_B2_D_RawTotal
import R1Z.PV_RDB2C_PV_B2_D_MulQm31Total
import R1Z.PV_RDB2C_PV_B2_C_MaterializeCompose
set_option autoImplicit false
namespace PV_B2_D_MaterializeTotal
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep PV_B2_C_ArrayTotal

theorem cell (w : host_weights.Weights) (k : Powers) (j : Usize)
    (hj : j.val < (1024#usize).val) : Total (host_weights.materialize_cell w k j) := by
  rcases k with ⟨k0,k1,k2,k3,k4,k5,k6⟩
  unfold host_weights.materialize_cell
  simp only [PV_B2_D_MulQm31Total.source,PV_B2_C_251WideTotal.WideExact_add]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact PV_B2_D_RawTotal.source _ _ _ (by decide) hj
    | apply PV_B2_C_ArrayTotal.bind
    | intro x

theorem cells (w : host_weights.Weights) (k : Powers) :
    PV_B2_C_MutationTotal.CellsTotal w k := by
  intro j hj
  exact cell w k j hj

/-- Complete Result success of the copied materialization kernel for every raw
weight, kappa, and initial caller array. Native allocation/original equality is
not asserted by this kernel theorem. -/
theorem source (w : host_weights.Weights) (kappa : E) (out : Out) :
    ∃ updated, pv_b2_materialize w kappa out = ok (core.result.Result.Ok (),updated) :=
  PV_B2_C_MaterializeCompose.source w kappa out (fun k _ => cells w k)
#print axioms cell
#print axioms cells
#print axioms source
end PV_B2_D_MaterializeTotal

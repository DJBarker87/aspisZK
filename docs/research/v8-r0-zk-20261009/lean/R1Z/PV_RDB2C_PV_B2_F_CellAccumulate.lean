import R1Z.PV_RDB2C_PV_B2_F_CellFold
set_option autoImplicit false
namespace PV_B2_F_CellAccumulate
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- Original inner loop, retaining its accumulator argument. -/
def original (w : host_weights.Weights) (k : Powers) (j : Usize) (initial : E) : Result E :=
  let (k0,k1,k2,k3,k4,k5,k6) := k
  [(k0,0#usize),(k1,1#usize),(k2,2#usize),(k3,3#usize),
   (k4,4#usize),(k5,5#usize),(k6,6#usize)].foldlM
    (fun (acc : E) (term : E × Usize) => do
      let q ← host_weights.raw_value w term.2 j
      let product ← host_weights.mul_qm31 term.1 q
      aspis_core.field.wide_exact.WideExact.add acc product) initial

theorem zero (w : host_weights.Weights) (k : Powers) (j : Usize) :
    original w k j aspis_core.field.wide_exact.WideExact.ZERO =
      PV_B2_F_CellFold.ordered w k j := rfl
#print axioms zero
end PV_B2_F_CellAccumulate

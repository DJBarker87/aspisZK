import R1Z.PV_RDB2C_PV_B2_D_MaterializeTotal
set_option autoImplicit false
namespace PV_B2_F_CellFold
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep

/-- Ordered seven-term source fold. The helpers remain the copied source
helpers; identifying frozen raw/powers/allocation remains separate work. -/
def ordered (w : host_weights.Weights) (k : Powers) (j : Usize) : Result E :=
  let (k0,k1,k2,k3,k4,k5,k6) := k
  [(k0,0#usize),(k1,1#usize),(k2,2#usize),(k3,3#usize),
   (k4,4#usize),(k5,5#usize),(k6,6#usize)].foldlM
    (fun (acc : E) (term : E × Usize) => do
      let q ← host_weights.raw_value w term.2 j
      let product ← host_weights.mul_qm31 term.1 q
      aspis_core.field.wide_exact.WideExact.add acc product)
    aspis_core.field.wide_exact.WideExact.ZERO

/-- Complete Result equality, including every failure and divergence, at every
index. Kernel reduction traverses only the fixed seven-element list; it does
not evaluate field operations, a transport table or the 1024-cell loop. -/
theorem source (w : host_weights.Weights) (k : Powers) (j : Usize) :
    host_weights.materialize_cell w k j = ordered w k j := by
  rcases k with ⟨k0,k1,k2,k3,k4,k5,k6⟩
  dsimp only [host_weights.materialize_cell,ordered]
  simp only [List.foldlM_cons,List.foldlM_nil,
    bind_assoc,bind_pure]
  rfl
#print axioms source
end PV_B2_F_CellFold

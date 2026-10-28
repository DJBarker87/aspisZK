import R1Z.PV_RDB2C_PV_B2_F_RawGuard
import R1Z.PV_RDB2C_PV_B2_F_CellAccumulate
set_option autoImplicit false
namespace PV_B2_F_FrozenCell
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- Frozen seven-kind fold with its independent raw match representation. -/
def original (w : host_weights.Weights) (k : Powers) (j : Usize) (initial : E) : Result E :=
  let (k0,k1,k2,k3,k4,k5,k6) := k
  [(k0,0#usize),(k1,1#usize),(k2,2#usize),(k3,3#usize),
   (k4,4#usize),(k5,5#usize),(k6,6#usize)].foldlM
    (fun (acc : E) (term : E × Usize) => do
      let q ← PV_B2_F_RawGuard.original w term.2 j
      let product ← host_weights.mul_qm31 term.1 q
      aspis_core.field.wide_exact.WideExact.add acc product) initial

theorem source (w : host_weights.Weights) (k : Powers) (j : Usize) (initial : E) :
    PV_B2_F_CellAccumulate.original w k j initial = original w k j initial := by
  unfold PV_B2_F_CellAccumulate.original original
  simp only [PV_B2_F_RawGuard.source]
#print axioms source
end PV_B2_F_FrozenCell

import R1Z.PV_CB3_Op249Staged
import R1Z.PV_CB3_StagedGammaTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op249Total
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem reference_total (ops : ExternalFuns) (block : Array U8 32#usize) :
    ∃ out, (PV_CB3_Op249Staged.selected ops).op249 block = ok out :=
  PV_CB3_StagedGammaTotal.gamma_total block

theorem reference_not_fail (ops : ExternalFuns) (block : Array U8 32#usize) (e : Error) :
    (PV_CB3_Op249Staged.selected ops).op249 block ≠ fail e := by
  obtain ⟨out,h⟩ := reference_total ops block
  rw [h]
  intro impossible
  cases impossible
#print axioms reference_total
#print axioms reference_not_fail
end R1Z.PV_CB3_Op249Total

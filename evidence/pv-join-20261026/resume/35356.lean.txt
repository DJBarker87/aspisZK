import R1Z.ProverRwSuccessGeneric
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Take
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Only the assigned callback is replaced; other fields remain available for composition. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { ops with op3 := ProverRwSuccessGeneric.take }
theorem op3_installed (ops : ExternalFuns) {T : Type}
    (inst : core.default.Default T) (x : T) :
    (selected ops).op3 inst x = (do
      let replacement ← inst.default
      .ok (x, replacement)) := rfl
theorem op3_success (ops : ExternalFuns) {T : Type}
    (inst : core.default.Default T) (x replacement : T)
    (h : inst.default = .ok replacement) :
    (selected ops).op3 inst x = .ok (x, replacement) := by
  rw [op3_installed, h]
  rfl
#print axioms op3_installed
#print axioms op3_success
end R1Z.PV_CB_Take

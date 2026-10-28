import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_DictionaryUpdate
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
theorem preserve (ops : ExternalFuns)
    (add mul : aspis_core.field.QM31 → aspis_core.field.QM31 → Result aspis_core.field.QM31)
    (ha : add=ops.op67) (hm : mul=ops.op69) :
    {ops with op67 := add,op69 := mul}=ops := by
  cases ha
  cases hm
  rfl
#print axioms preserve
end R1Z.PV_DictionaryUpdate

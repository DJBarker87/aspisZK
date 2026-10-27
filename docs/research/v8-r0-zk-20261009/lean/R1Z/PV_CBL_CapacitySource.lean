import R1Z.PV_CBL_CapacityValue
import R1Z.PV_CBL_CallbackBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_CapacitySource
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op30 := PV_CBL_CapacityValue.reference}
theorem op30_source (ops : ExternalFuns) (n : Usize) :
    (selected ops).op30 n = PV_CBL_CapacityValue.reference n := rfl
theorem op30_value (ops : ExternalFuns) (n : Usize) :
    (selected ops).op30 n = ok "" := PV_CBL_CapacityValue.value n
#print axioms op30_source
#print axioms op30_value
end R1Z.PV_CBL_CapacitySource

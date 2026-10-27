import R1Z.PV_CB_Op229Transport
import R1Z.PV_Join_Op20Value
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_NativeOp20Carrier
open Aeneas Aeneas.Std ProverRwFull
/-- Specialize the checked structural carrier bijection to the actual op229
native ExternalTypes dictionary and CB3's installed op20 dictionary. -/
def carrier (base : ExternalTypes) :
    @ExternalTypes.op20 (PV_CB_Op229Transport.native base) ≃
      @ExternalTypes.op20 (PV_CB3_Afterstate.selectedTypes base) :=
  PV_Join_Op20Value.carrier
#print axioms carrier
end R1Z.PV_Join_NativeOp20Carrier

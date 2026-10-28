import R1Z.PV_CB_Op109Exact
import R1Z.PV_RDCD_CanonicalSource
import R1Z.PV_RDCD_Op107Audit
import R1Z.PV_RDCD_ShiftBound
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_Op109Audit
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- The retained whole Result/Option source interface; no canonical-input restriction. -/
theorem source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (PV_CB_Op109Exact.selected ops).op109 x = (do
      let value ← PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv
        (PV_CB_Op109Transport.encodeW x)
      ok (value.map PV_CB_Op109Transport.decodeW)) := PV_CB_Op109Exact.op109_source ops x
#print axioms source
#print axioms PV_RDCD_CanonicalSource.reference
#print axioms PV_RDCD_CanonicalSource.environment_unique
#print axioms PV_RDCD_CanonicalSource.drop_frame
#print axioms PV_CB_Op109CanonicalBinding.reference_equation
#print axioms PV_CB_Op109Transport.native_wide_roundtrip
#print axioms PV_CB_Op109Transport.extracted_wide_roundtrip
end R1Z.PV_RDCD_Op109Audit

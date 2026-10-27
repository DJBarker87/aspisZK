import R1Z.PV_CB_Op109Transport
import R1Z.PV_CB_Op109RefFuns
import R1Z.PV_CB_Op109RefTransport
/-! P6 helper binding. The native constructor gate compares both arbitrary
QM31 inputs through its two output coordinates. The current extracted new
body calls canonical_qm31 independently for those coordinates. The reference
source and native receipt are recorded in RESUME3-OP109-P6-PROGRESS.json.
The complete inverse source equation is a separate target. -/
set_option autoImplicit false

namespace PV_CB_ShippedOp109
open Aeneas Aeneas.Std Result

@[rust_fun "aspis_core::field::wide_exact::canonical_qm31"]
def aspis_core.field.wide_exact.canonical_qm31
    (value : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let result ← PV_CB_ShippedOp109Ref.owned_wide_new.canonical_qm31
    (R1Z.PV_CB_Op109RefTransport.encode (R1Z.PV_CB_Op109Transport.decode value))
  ok (R1Z.PV_CB_Op109Transport.encode (R1Z.PV_CB_Op109RefTransport.decode result))
end PV_CB_ShippedOp109

namespace R1Z.PV_CB_Op109CanonicalBinding
open Aeneas Aeneas.Std Result

theorem reference_equation (value : PV_CB_ShippedOp109.aspis_core.field.QM31) :
    PV_CB_ShippedOp109.aspis_core.field.wide_exact.canonical_qm31 value = (do
      let result ← PV_CB_ShippedOp109Ref.owned_wide_new.canonical_qm31
        (PV_CB_Op109RefTransport.encode (PV_CB_Op109Transport.decode value))
      ok (PV_CB_Op109Transport.encode (PV_CB_Op109RefTransport.decode result))) := rfl

#print axioms reference_equation
end R1Z.PV_CB_Op109CanonicalBinding

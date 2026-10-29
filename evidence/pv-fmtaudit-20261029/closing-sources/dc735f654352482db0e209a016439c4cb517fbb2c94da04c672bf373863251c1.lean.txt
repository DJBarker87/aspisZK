import R1Z.PV_CB_Op118Exact
import R1Z.PV_RDCD_PointsStep
import R1Z.PV_RDCD_Op107Audit
import R1Z.PV_RDCD_ShiftBound
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_Op118Audit
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
theorem source (ops : ExternalFuns) (x : Array aspis_core.field.QM31 10#usize) :
    (PV_CB_Op118Exact.selected ops).op118 x = (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points
        (PV_CB_Op118Transport.encodeArray x)
      ok (PV_CB_Op118Transport.decodePoints value)) := PV_CB_Op118Exact.op118_source ops x
#print axioms source
#print axioms PV_RDCD_PointsStep.emitted
#print axioms PV_RDCD_Range194.next_back
#print axioms PV_RDCD_Range194.reverse_dispatch
#print axioms PV_CB_Op118Transport.native_array_roundtrip
#print axioms PV_CB_Op118Transport.extracted_array_roundtrip
#print axioms PV_CB_Op118Transport.native_points_roundtrip
#print axioms PV_CB_Op118Transport.extracted_points_roundtrip
end R1Z.PV_RDCD_Op118Audit

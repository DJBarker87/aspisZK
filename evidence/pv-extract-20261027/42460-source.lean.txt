import R1Z.PV_Ext_Closed_25_compress
import R1Z.ProverRwP6CompressSource
import R1Z.PV_Ext_IndexBridge
import R1Z.PV_Ext_DiagnosticOp36Funs
import R1Z.PV_Ext_DiagnosticOp224Funs
import R1Z.PV_Ext_FieldBridge_CM31_mul
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Ext_ClosedCandidate
open Aeneas Aeneas.Std Result ProverRwFull
namespace Src
abbrev compress := PV_Ext_IndexClosed.compress_tagged_tuple
abbrev cm_from := PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31
abbrev qm_from := PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31
abbrev add := PV_Ext_IndexClosed.aspis_core.field.QM31.add
abbrev mul := PV_Ext_IndexClosed.aspis_core.field.QM31.mul
abbrev scale := PV_Ext_IndexClosed.aspis_core.field.QM31.mul_m31
end Src
variable [ExternalTypes]
/-- Installs the five *closed candidate* arithmetic dependencies. This neither
    installs op223 nor identifies a shipped callback with the candidate. -/
@[reducible] def fields (ops : ExternalFuns) : ExternalFuns :=
  {ops with
    op61 := Src.cm_from
    op66 := Src.qm_from
    op67 := Src.add
    op69 := Src.mul
    op70 := Src.scale}

/-- Arbitrary-input, complete Result equality for the index candidate against
    P6 using its extracted arithmetic. No canonicality or desired-output premise. -/
theorem candidate_reference (ops : ExternalFuns) :
    Src.compress = @ProverRwP6CompressSource.compress _ (fields ops) := rfl

#print axioms candidate_reference
end R1Z.PV_Ext_ClosedCandidate

-- Final frozen closure audit; diagnostic function parameters stay explicit.
#print axioms PV_Ext_IndexClosed.aspis_core.field.P
#print axioms PV_Ext_IndexClosed.aspis_core.field.ct.subtract_p
#print axioms PV_Ext_IndexClosed.aspis_core.field.ct.reduce64
#print axioms PV_Ext_IndexClosed.aspis_core.field.ct.add
#print axioms PV_Ext_IndexClosed.aspis_core.field.ct.sub
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.ZERO
#print axioms PV_Ext_IndexClosed.aspis_core.field.reduce_u64
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.mul
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.reduce_u64
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.add
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.double
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.add
#print axioms PV_Ext_IndexClosed.aspis_core.field.M31.sub
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.sub
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.mul
#print axioms PV_Ext_IndexClosed.aspis_core.field.CM31.mul_m31
#print axioms PV_Ext_IndexClosed.aspis_core.field.mul_by_r
#print axioms PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31
#print axioms PV_Ext_IndexClosed.aspis_core.field.QM31.add
#print axioms PV_Ext_IndexClosed.aspis_core.field.QM31.mul
#print axioms PV_Ext_IndexClosed.aspis_core.field.QM31.mul_m31
#print axioms PV_Ext_IndexClosed.compress_tagged_tuple_loop.body
#print axioms PV_Ext_IndexClosed.compress_tagged_tuple_loop
#print axioms PV_Ext_IndexClosed.compress_tagged_tuple
#print axioms R1Z.PV_Ext_FieldBridge.P
#print axioms R1Z.PV_Ext_FieldBridge.ct_subtract_p
#print axioms R1Z.PV_Ext_FieldBridge.ct_reduce64
#print axioms R1Z.PV_Ext_FieldBridge.ct_add
#print axioms R1Z.PV_Ext_FieldBridge.ct_sub
#print axioms R1Z.PV_Ext_FieldBridge.M31_ZERO
#print axioms R1Z.PV_Ext_FieldBridge.reduce_u64
#print axioms R1Z.PV_Ext_FieldBridge.M31_mul
#print axioms R1Z.PV_Ext_FieldBridge.M31_reduce_u64
#print axioms R1Z.PV_Ext_FieldBridge.M31_add
#print axioms R1Z.PV_Ext_FieldBridge.M31_double
#print axioms R1Z.PV_Ext_FieldBridge.CM31_ZERO
#print axioms R1Z.PV_Ext_FieldBridge.CM31_from_m31
#print axioms R1Z.PV_Ext_FieldBridge.CM31_add
#print axioms R1Z.PV_Ext_FieldBridge.M31_sub
#print axioms R1Z.PV_Ext_FieldBridge.CM31_sub
#print axioms R1Z.PV_Ext_FieldBridge.CM31_mul
#print axioms R1Z.PV_Ext_IndexBridge.reference
#print axioms R1Z.PV_Ext_IndexBridge.loop_reference
#print axioms R1Z.PV_Ext_IndexBridge.body_reference

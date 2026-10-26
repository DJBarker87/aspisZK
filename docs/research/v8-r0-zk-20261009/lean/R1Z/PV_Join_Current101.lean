import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op101Exact
import R1Z.PV_CB_CurrentNeg
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current101
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op101Transport ProverRwDictionaryTower

theorem scalar (x : U32) : PV_CB_ShippedOp101.aspis_core.field.M31.neg x = AspisR1ProducerRelease47.field.M31.neg x := by
  refine Eq.trans ?_ (PV_CB_CurrentNeg.native x)
  unfold PV_CB_ShippedOp101.aspis_core.field.M31.neg PV_CB_ShippedOp101.aspis_core.field.ct.neg
    PV_CB_CurrentNeg.source ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg
    ProverRwP7CurrentFieldSource.aspis_core.field.ct.neg
    PV_CB_ShippedOp101.aspis_core.field.P ProverRwP7CurrentFieldSource.aspis_core.field.P
  rfl

theorem complex (x : RC) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.CM31.neg x; ok (decodeC y)) =
      ProverRwSuccessInverseSource.field.CM31.neg (decodeC x) := by
  simp only [PV_CB_ShippedOp101.aspis_core.field.CM31.neg,scalar,decodeC,
    ProverRwSuccessInverseSource.field.CM31.neg,AspisR1ProducerRelease47.field.CM31.neg,
    toC,fromC,mapResult_bind,bind_assoc_eq,bind_tc_ok]

theorem quartic (x : R) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.neg x; ok (decode y)) =
      ProverRwSuccessInverseSource.field.QM31.neg (decode x) := by
  simp only [PV_CB_ShippedOp101.aspis_core.field.QM31.neg,decode,ProverRwSuccessInverseSource.field.QM31.neg]
  rw [← complex,← complex]
  simp only [bind_assoc_eq,bind_tc_ok]

variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (ProverRwP6BodyStore.selected ops).op101 x = (PV_CB_Op101Exact.selected ops).op101 x := by
  change ProverRwSuccessInverseSource.field.QM31.neg x = _
  rw [PV_CB_Op101Exact.op101_source]
  change _ = (do let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.neg (encode x); ok (decode y))
  rw [quartic,native_roundtrip]
theorem op101_source (ops : ExternalFuns) (x : aspis_core.field.QM31) :
    (ProverRwP6BodyStore.selected ops).op101 x = (do
      let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg (encode x)
      ok (decode y)) :=
  (selected_bridge ops x).trans (PV_CB_Op101Exact.op101_source ops x)
#print axioms scalar
#print axioms complex
#print axioms quartic
#print axioms selected_bridge
#print axioms op101_source
end R1Z.PV_Join_Current101

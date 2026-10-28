import R1Z.ProverRwP6BodyStore
import R1Z.PV_CB_Op100Exact
import R1Z.PV_Join_NegTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Current100
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op100Transport ProverRwDictionaryTower

theorem scalar (x : U32) : PV_CB_ShippedOp100.aspis_core.field.M31.neg x = AspisR1ProducerRelease47.field.M31.neg x := by
  exact PV_Join_NegTransport.scalar100 x

theorem complex (x : RC) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.CM31.neg x; ok (decodeC y)) =
      ProverRwSuccessInverseSource.field.CM31.neg (decodeC x) := by
  have transport := congrArg
    (fun result => do let value ← result; ok (fromC value))
      (PV_Join_NegTransport.complex100 x)
  simpa only [ProverRwSuccessInverseSource.field.CM31.neg,
    PV_Join_NegTransport.decodeC100,decodeC,mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC] using transport

theorem quartic (x : R) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.QM31.neg x; ok (decode y)) =
      ProverRwSuccessInverseSource.field.QM31.neg (decode x) := by
  simp only [PV_CB_ShippedOp100.aspis_core.field.QM31.neg,decode,ProverRwSuccessInverseSource.field.QM31.neg]
  simp_rw [← complex]
  simp only [bind_assoc_eq,bind_tc_ok]

variable [ExternalTypes]
theorem wide (x : RW) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.neg x; ok (decodeW y)) =
      ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.neg (decodeW x) := by
  simp only [PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.neg,decodeW,
    ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.neg]
  simp_rw [← quartic]
  simp only [bind_assoc_eq,bind_tc_ok]
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (ProverRwP6BodyStore.selected ops).op100 x = (PV_CB_Op100Exact.selected ops).op100 x := by
  change ProverRwSuccessNativePorts.aspis_core.field.wide_exact.WideExact.neg x = _
  rw [PV_CB_Op100Exact.op100_source]
  change _ = (do let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.neg (encodeW x); ok (decodeW y))
  rw [wide,native_wide_roundtrip]
#print axioms wide
theorem op100_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (ProverRwP6BodyStore.selected ops).op100 x = (do
      let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg (encodeW x)
      ok (decodeW y)) :=
  (selected_bridge ops x).trans (PV_CB_Op100Exact.op100_source ops x)
#print axioms scalar
#print axioms complex
#print axioms quartic
#print axioms selected_bridge
#print axioms op100_source
end R1Z.PV_Join_Current100

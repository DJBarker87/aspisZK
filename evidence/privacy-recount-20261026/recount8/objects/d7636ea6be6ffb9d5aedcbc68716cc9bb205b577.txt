import R1Z.ProverRwSuccessInverseSource
import R1Z.PV_Join_NegTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_NativeNeg101
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
abbrev RC := PV_CB_ShippedOp101.aspis_core.field.CM31
abbrev R := PV_CB_ShippedOp101.aspis_core.field.QM31
def decodeC (x : RC) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def decode (x : R) : aspis_core.field.QM31 := ⟨decodeC x.c0,decodeC x.c1⟩

theorem scalar (x : U32) : PV_CB_ShippedOp101.aspis_core.field.M31.neg x = AspisR1ProducerRelease47.field.M31.neg x := by
  exact PV_Join_NegTransport.scalar101 x

theorem complex (x : RC) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.CM31.neg x; ok (decodeC y)) =
      ProverRwSuccessInverseSource.field.CM31.neg (decodeC x) := by
  have transport := congrArg
    (fun result => do let value ← result; ok (fromC value))
      (PV_Join_NegTransport.complex101 x)
  simpa only [ProverRwSuccessInverseSource.field.CM31.neg,
    PV_Join_NegTransport.decodeC101,decodeC,mapResult_bind,bind_assoc_eq,bind_tc_ok,toC,fromC] using transport

theorem quartic (x : R) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.neg x; ok (decode y)) =
      ProverRwSuccessInverseSource.field.QM31.neg (decode x) := by
  simp only [PV_CB_ShippedOp101.aspis_core.field.QM31.neg,decode,ProverRwSuccessInverseSource.field.QM31.neg]
  simp_rw [← complex]
  simp only [bind_assoc_eq,bind_tc_ok]

#print axioms scalar
#print axioms complex
#print axioms quartic
end R1Z.PV_Join_NativeNeg101

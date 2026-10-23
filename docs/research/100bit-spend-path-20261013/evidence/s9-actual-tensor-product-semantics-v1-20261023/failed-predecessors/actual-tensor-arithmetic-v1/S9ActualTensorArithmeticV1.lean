import S9ActualPairQMHelperTransportV1
import KpowersCurrentQMSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualTensorArithmeticV1
open AspisR1S9ActualPairQMHelperTransportV1
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM

def decode (x : Q) : ExactQM :=
  AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.decode (toHelperQ x)

/-- Interpret the SAME successful native tensor multiplication. The input
canonicality premises are discharged by the existing actual prefix invariant;
this is multiplication semantics, not an inference from output canonicality. -/
theorem native_mul_success_exact (x y z : Q) (hx : Canonical x) (hy : Canonical y)
    (h : aspis_core.field.QM31.mul x y = .ok z) :
    Canonical z ∧ decode z = decode x * decode y := by
  have hm := actual_pair_qm_mul_to_installed_helper x y hx hy
  rw [h] at hm
  have hc : @AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9HelperP6PowerSemanticsV1.currentQMOps
      (toHelperQ x) (toHelperQ y) = .ok (toHelperQ z) := hm.symm
  have hout := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.mul_success
    (toHelperQ x) (toHelperQ y) (toHelperQ z) hx hy hc
  exact hout

theorem native_one_decode : decode aspis_core.field.QM31.ONE = 1 := by
  have h := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics.decode_one
  exact h

#print axioms native_mul_success_exact
#print axioms native_one_decode
end AspisR1S9ActualTensorArithmeticV1

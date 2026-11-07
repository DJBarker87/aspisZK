import NNG_InstallBase
import NLU_FieldValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_InstallArithmetic
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Transport
open NMP_ResultTransport (outer outer_inverse)
def add (x y : aspis_core.field.QM31) := outer fromT1 (FIp_SemanticArithmetic.add (toT1 x) (toT1 y))
def mul (x y : aspis_core.field.QM31) := outer fromT1 (FIp_SemanticArithmetic.mul (toT1 x) (toT1 y))
theorem add_same (x y : aspis_core.field.QM31) :
 outer toT1 (add x y)=FIp_SemanticArithmetic.add (toT1 x) (toT1 y) :=
 outer_inverse fromT1 toT1 fromT1_inverse _
theorem mul_same (x y : aspis_core.field.QM31) :
 outer toT1 (mul x y)=FIp_SemanticArithmetic.mul (toT1 x) (toT1 y) :=
 outer_inverse fromT1 toT1 fromT1_inverse _
/-- Paired emitted multiplication law, on precisely canonical own operands.
No multiplication is unrolled or verified in Kani. -/
theorem mul_value (reservation : NP6_StdModel.Reservation) (x y : aspis_core.field.QM31)
 (hx : JFv_RoundArithmetic.Canonical (toT1 x)) (hy : JFv_RoundArithmetic.Canonical (toT1 y)) :
 ∃ z,mul x y=.ok z ∧ JFv_RoundArithmetic.Canonical (toT1 z) ∧
 FIv_NativeValue.decode (FIq_Carriers.toQ (toT1 z))=
 FIv_NativeValue.decode (FIq_Carriers.toQ (toT1 x))*FIv_NativeValue.decode (FIq_Carriers.toQ (toT1 y)) := by
 obtain ⟨z,returned,canon,value⟩ := NLU_FieldValues.mul_value reservation (toT1 x) (toT1 y) hx hy
 refine ⟨fromT1 z,?_,?_,?_⟩
 · change outer fromT1 (FIp_SemanticArithmetic.mul (toT1 x) (toT1 y))=ok (fromT1 z)
   change FIp_SemanticArithmetic.mul (toT1 x) (toT1 y)=ok z at returned
   rw [returned];rfl
 · rw [fromT1_inverse];exact canon
 · rw [fromT1_inverse];exact value
#print axioms add_same
#print axioms mul_same
#print axioms mul_value
end AspisR1.NNG_InstallArithmetic

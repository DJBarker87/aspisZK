import NLU_TerminalCanonical
import NLU_FieldLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_FieldValues
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
abbrev Q := aspis_core.field.QM31
def fromNative : Result FIv_NativeArithmetic.NQ → Result Q
 | .ok q=>ok (fromQ q)
 | .fail err=>.fail err
 | .div=>.div
theorem mul_transport (x y : Q) :
 FIp_SemanticArithmetic.mul x y=fromNative (FIq_Native.field.QM31.mul (toQ x) (toQ y)) := by
 have same : AspisR1SelectedMaskProbe.field.QM31.mul
  (FIp_SemanticArithmetic.toProbe x) (FIp_SemanticArithmetic.toProbe y)=
  FIv_Map.map FIv_NativeArithmetic.qm (FIq_Native.field.QM31.mul (toQ x) (toQ y)) :=
  (FIv_NativeQM.mul (toQ x) (toQ y)).symm
 unfold FIp_SemanticArithmetic.mul
 rw [same]
 cases h : FIq_Native.field.QM31.mul (toQ x) (toQ y) <;> rfl
theorem add_transport (x y : Q) :
 FIp_SemanticArithmetic.add x y=fromNative (FIq_Native.field.QM31.add (toQ x) (toQ y)) := by
 have same : AspisR1SelectedMaskProbe.field.QM31.add
  (FIp_SemanticArithmetic.toProbe x) (FIp_SemanticArithmetic.toProbe y)=
  FIv_Map.map FIv_NativeArithmetic.qm (FIq_Native.field.QM31.add (toQ x) (toQ y)) :=
  (FIv_NativeQM.add (toQ x) (toQ y)).symm
 unfold FIp_SemanticArithmetic.add
 rw [same]
 cases h : FIq_Native.field.QM31.add (toQ x) (toQ y) <;> rfl
/-- Paired emitted value law for the opaque native multiplication call. No
multiplication is evaluated or proved in Kani. The output is canonical and
has exactly the existing probe/field product on this canonical input domain. -/
theorem mul_value (r : NP6_StdModel.Reservation) (x y : Q)
 (hx : JFv_RoundArithmetic.Canonical x) (hy : JFv_RoundArithmetic.Canonical y) :
 ∃ z,(IDa_Deployed.boundaries r).mul x y=ok z ∧ JFv_RoundArithmetic.Canonical z ∧
 FIv_NativeValue.decode (toQ z)=FIv_NativeValue.decode (toQ x)*FIv_NativeValue.decode (toQ y) := by
 obtain ⟨z,returned,canonical,value⟩:=NJB_StubLaws.qm_mul (toQ x) (toQ y)
  (NLU_Terminal.canonical_to_native x hx) (NLU_Terminal.canonical_to_native y hy)
 refine ⟨fromQ z,?_,NLU_Terminal.canonical_from_native z canonical,?_⟩
 · change FIp_SemanticArithmetic.mul x y=ok (fromQ z)
   rw [mul_transport,returned]
   rfl
 · rw [nq_roundtrip]
   exact value
theorem add_value (r : NP6_StdModel.Reservation) (x y : Q)
 (hx : JFv_RoundArithmetic.Canonical x) (hy : JFv_RoundArithmetic.Canonical y) :
 ∃ z,(IDa_Deployed.boundaries r).add x y=ok z ∧ JFv_RoundArithmetic.Canonical z ∧
 FIv_NativeValue.decode (toQ z)=FIv_NativeValue.decode (toQ x)+FIv_NativeValue.decode (toQ y) := by
 obtain ⟨z,returned,canonical,value⟩:=NJB_StubLaws.qm_add (toQ x) (toQ y)
  (NLU_Terminal.canonical_to_native x hx) (NLU_Terminal.canonical_to_native y hy)
 refine ⟨fromQ z,?_,NLU_Terminal.canonical_from_native z canonical,?_⟩
 · change FIp_SemanticArithmetic.add x y=ok (fromQ z)
   rw [add_transport,returned]
   rfl
 · rw [nq_roundtrip]
   exact value
#print axioms mul_transport
#print axioms add_transport
#print axioms mul_value
#print axioms add_value
end AspisR1.NLU_FieldValues
end

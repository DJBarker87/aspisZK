import NDE_Reference12.Funs
import NDE_VariantBridge
import RPu_FIq_Native08
import RPv_FIv_Arithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_SimpleBridge

theorem binary (copy : core.marker.Copy FIq_Native.field.QM31)
    (high : FIq_Native.field.QM31) (weight : U32)
    (hw : weight = 0#u32 ∨ weight = 1#u32)
    (hc : AspisR1.FIv_NativeValue.Canon high) :
    ∃ out, NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight = ok out ∧
      AspisR1.FIv_NativeValue.Canon out ∧
      AspisR1.FIv_NativeValue.decode out = AspisR1.FIv_NativeValue.decode high * (weight.val : AspisR1.FIv_NativeValue.K) := by
  rcases hw with rfl | rfl
  · refine ⟨FIq_Native.field.QM31.ZERO,?_,AspisR1.FIv_NativeValue.zero.1,?_⟩
    · rfl
    · simp only [show (0#u32).val=0 from rfl,Nat.cast_zero,mul_zero,AspisR1.FIv_NativeValue.zero.2]
  · refine ⟨high,rfl,hc,?_⟩
    simp only [show (1#u32).val=1 from rfl,Nat.cast_one,mul_one]

theorem variant (v : NDE_VariantBridge.V) :
    NDE_Reference12.variant_output_ref (NDE_VariantBridge.isWithdrawal v) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.variant_expected_output v := by
  cases v <;> rfl

#print axioms binary
#print axioms variant
end NDE_SimpleBridge

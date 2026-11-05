import NHU_COMBINED_IMPORT
import NDE_SimpleBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_SelectedBinary
/-- Existing extracted safe generic reference, instantiated at the SAME four-word record.
The optimized original helper has no retained emitted declaration. -/
theorem reference (copy : core.marker.Copy FIq_Native.field.QM31)
 (high : FIq_Native.field.QM31) (weight : U32) :
 NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight=
 ok (if weight=1#u32 then high else FIq_Native.field.QM31.ZERO) := by
 unfold NDE_Reference12.selected_binary_ref
 split <;> rfl
/-- Caller-established binary weights identify the adopted multiplication value. -/
theorem result (copy : core.marker.Copy FIq_Native.field.QM31)
 (high : FIq_Native.field.QM31) (weight : U32) (canonical : FIv_NativeValue.Canon high)
 (bounded : weight.val≤1) :
 ∃ out, NDE_Reference12.selected_binary_ref copy high FIq_Native.field.QM31.ZERO weight=ok out ∧
 FIv_NativeValue.Canon out ∧
 FIv_NativeValue.decode out=FIv_NativeValue.decode high*(weight.val : FIv_NativeValue.K) := by
 apply NDE_SimpleBridge.binary copy high weight _ canonical
 rcases (by omega : weight.val=0 ∨ weight.val=1) with h|h
 · exact Or.inl (UScalar.eq_of_val_eq h)
 · exact Or.inr (UScalar.eq_of_val_eq h)
#print axioms reference
#print axioms result
end AspisR1.NIH_SelectedBinary

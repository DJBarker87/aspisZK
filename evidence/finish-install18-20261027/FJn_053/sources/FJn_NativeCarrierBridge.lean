import FIr_NativeArray
import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_NativeCarrierBridge
open Aeneas Aeneas.Std
/-- The two retained proof namespaces decode the SAME four source limbs. -/
theorem decode (x : FIq_Native.field.QM31) : FIr_NativeValue.decode x=FIv_NativeValue.decode x := rfl
theorem canonical (x : FIq_Native.field.QM31) : FIr_NativeValue.Canon x ↔ FIv_NativeValue.Canon x := Iff.rfl
theorem array {N : Usize} (a : Array FIq_Native.field.QM31 N) (i : Nat) :
    FIr_NativeArray.value a i=FIv_NativeArray.value a i := rfl
#print axioms decode
#print axioms canonical
#print axioms array
end AspisR1.FJn_NativeCarrierBridge
end

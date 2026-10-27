import RPu_FJk_MaskValueStep
import R0P.Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_MaskModel
open Aeneas Aeneas.Std Result FIq_Native
/-- These are seven bounded16-bit mask plans,not field or recurrence evaluation. -/
theorem m6144 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [11, 12] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 6144 := by
  rfl
#print axioms m6144
theorem m6145 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [0, 11, 12] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 6145 := by
  rfl
#print axioms m6145
theorem m4097 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [0, 12] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 4097 := by
  rfl
#print axioms m4097
theorem m2048 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [11] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 2048 := by
  rfl
#print axioms m2048
theorem m2049 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [0, 11] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 2049 := by
  rfl
#print axioms m2049
theorem m1749 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [0, 2, 4, 6, 7, 9, 10] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 1749 := by
  rfl
#print axioms m1749
theorem m26214 (a : Array field.QM31 16#usize) :
    FJk_MaskValueStep.model a [1, 2, 5, 6, 9, 10, 13, 14] 0 =
    R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) 26214 := by
  rfl
#print axioms m26214
end AspisR1.FJk_MaskModel
end

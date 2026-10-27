import RPv_FJk_MaskValues
import RPv_FJk_MaskModel
import RPv_JGa_ActiveMaskKinds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_ActiveMaskValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
/-- Actual native low-mask VALUE for every mask read by the installed active loop. -/
theorem value (a : Array field.QM31 16#usize) (mask : U16) (out : field.QM31)
    (ha : canonical a) (hm : mask∈constants.ACTIVE_ROW_MASKS.val)
    (run : selector_mask_sum_16 a mask=ok out) :
    Canon out ∧ decode out=R0P.copySelectorMaskSum16 (fun i=>FIv_NativeArray.value a i.val) mask.val := by
  have kinds := JGa_ActiveMaskKinds.all mask hm
  rcases kinds with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact ⟨(FJk_MaskValues.s6144 a ha out run).1,(FJk_MaskValues.s6144 a ha out run).2.trans (FJk_MaskModel.m6144 a)⟩
    | exact ⟨(FJk_MaskValues.s6145 a ha out run).1,(FJk_MaskValues.s6145 a ha out run).2.trans (FJk_MaskModel.m6145 a)⟩
    | exact ⟨(FJk_MaskValues.s4097 a ha out run).1,(FJk_MaskValues.s4097 a ha out run).2.trans (FJk_MaskModel.m4097 a)⟩
    | exact ⟨(FJk_MaskValues.s2048 a ha out run).1,(FJk_MaskValues.s2048 a ha out run).2.trans (FJk_MaskModel.m2048 a)⟩
    | exact ⟨(FJk_MaskValues.s2049 a ha out run).1,(FJk_MaskValues.s2049 a ha out run).2.trans (FJk_MaskModel.m2049 a)⟩
    | exact ⟨(FJk_MaskValues.s1749 a ha out run).1,(FJk_MaskValues.s1749 a ha out run).2.trans (FJk_MaskModel.m1749 a)⟩
    | exact ⟨(FJk_MaskValues.s26214 a ha out run).1,(FJk_MaskValues.s26214 a ha out run).2.trans (FJk_MaskModel.m26214 a)⟩
#print axioms value
end AspisR1.FJk_ActiveMaskValue
end

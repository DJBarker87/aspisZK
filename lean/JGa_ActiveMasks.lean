import JGa_MaskLoops
import JGa_ActiveMaskKinds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ActiveMasks
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (a : Array field.QM31 16#usize) (mask : U16) (ha : canonical a)
    (hm : mask∈constants.ACTIVE_ROW_MASKS.val) :
    ∃ out,selector_mask_sum_16 a mask=ok out ∧ Canon out := by
  have kinds := JGa_ActiveMaskKinds.all mask hm
  rcases kinds with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact JGa_MaskLoops.s6144 a ha | exact JGa_MaskLoops.s6145 a ha |
    exact JGa_MaskLoops.s4097 a ha | exact JGa_MaskLoops.s2048 a ha | exact JGa_MaskLoops.s2049 a ha |
    exact JGa_MaskLoops.s1749 a ha | exact JGa_MaskLoops.s26214 a ha
#print axioms source
end AspisR1.JGa_ActiveMasks
end

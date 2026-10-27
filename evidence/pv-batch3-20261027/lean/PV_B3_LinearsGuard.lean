import PV_B3_LinearsCounter
namespace PV_B3_LinearsGuard
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_117 PV_B3_LinearsCounter
set_option autoImplicit false
 theorem continued (point : Array Q 10#usize) (a b : Q) (i : Usize) (next : State)
    (h : host_arithmetic.selected_mask_linears_loop.body point a b i = ok (cont next)) :
    0 < i.val ∧ next.2.2 = Usize.wrapping_sub i 1#usize := by
  have hc := body_counter point a b i (cont next) h
  change next.2.2 = Usize.wrapping_sub i 1#usize at hc
  unfold host_arithmetic.selected_mask_linears_loop.body at h
  split at h
  · rename_i hi
    exact ⟨hi,hc⟩
  · cases h
#print axioms continued
end PV_B3_LinearsGuard

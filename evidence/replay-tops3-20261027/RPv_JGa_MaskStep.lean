import RPv_JFy_Steps
import RPu_FIq_Native13
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_MaskStep
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem zero (a : Array field.QM31 16#usize) (sum : field.QM31) :
    selector_mask_sum_16_loop a 0#u16 false sum=ok sum := by
  rw [selector_mask_sum_16_loop]
  rfl
#print axioms zero

theorem source (a : Array field.QM31 16#usize) (sum : field.QM31)
    (mask sub next : U16) (pos : U32) (index : Usize)
    (ha : canonical a) (hs : Canon sum) (hi : index.val<16)
    (hnz : (mask != 0#u16)=true) (hpos : core.num.U16.trailing_zeros mask=ok pos)
    (hindex : UScalar.cast .Usize pos=index) (hsub : mask-1#u16=ok sub) (hnext : mask &&& sub=next)
    (tail : ∀ s,Canon s → ∃ out,selector_mask_sum_16_loop a next false s=ok out ∧ Canon out) :
    ∃ out,selector_mask_sum_16_loop a mask false sum=ok out ∧ Canon out := by
  obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read a index hi ha
  obtain ⟨s,hadd,hsc,_⟩ := FIv_PreparedTotal.add sum q hs hqc
  obtain ⟨out,hout,hoc⟩ := tail s hsc
  refine ⟨out,?_,hoc⟩
  rw [selector_mask_sum_16_loop,if_pos hnz,hpos,bind_tc_ok]
  simp only [hindex,lift,bind_tc_ok,Bool.false_eq_true,↓reduceIte]
  rw [hq,bind_tc_ok,hadd,bind_tc_ok,hsub,bind_tc_ok]
  simp only [hnext,lift,bind_tc_ok]
  exact hout
#print axioms source
end AspisR1.JGa_MaskStep
end

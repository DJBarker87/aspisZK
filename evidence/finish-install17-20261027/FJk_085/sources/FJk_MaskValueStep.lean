import JGa_MaskStep
import FIv_NativeArray
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_MaskValueStep
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
def model (a : Array field.QM31 16#usize) (is : List Nat) (seed : K) : K :=
  is.foldl (fun acc i=>acc+FIv_NativeArray.value a i) seed
theorem zero (a : Array field.QM31 16#usize) (before out : field.QM31)
    (hb : Canon before) (run : selector_mask_sum_16_loop a 0#u16 false before=ok out) :
    Canon out ∧ decode out=model a [] (decode before) := by
  rw [JGa_MaskStep.zero] at run
  cases Result.ok.inj run
  exact ⟨hb,rfl⟩
/-- One original bit-clearing step; concrete mask plans are supplied separately. -/
theorem value (a : Array field.QM31 16#usize) (sum out : field.QM31)
    (mask sub next : U16) (pos : U32) (index : Usize) (is : List Nat)
    (ha : canonical a) (hs : Canon sum) (hi : index.val<16)
    (hnz : (mask != 0#u16)=true) (hpos : core.num.U16.trailing_zeros mask=ok pos)
    (hindex : UScalar.cast .Usize pos=index) (hsub : mask-1#u16=ok sub) (hnext : mask &&& sub=next)
    (tail : ∀ s,Canon s → selector_mask_sum_16_loop a next false s=ok out →
      Canon out ∧ decode out=model a is (decode s))
    (run : selector_mask_sum_16_loop a mask false sum=ok out) :
    Canon out ∧ decode out=model a (index.val::is) (decode sum) := by
  rw [selector_mask_sum_16_loop,if_pos hnz,hpos,bind_tc_ok] at run
  simp only [hindex,lift,bind_tc_ok,Bool.false_eq_true,↓reduceIte] at run
  obtain ⟨q,rq,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨s,rs,run⟩ := FIv_Map.bind_success _ _ _ run
  rw [hsub,bind_tc_ok] at run
  simp only [hnext,lift,bind_tc_ok] at run
  have cq := FIv_NativeArray.canonical a index q ha rq
  have sv := FIv_NativeValue.add sum q s hs cq rs
  have got := tail s sv.1 run
  refine ⟨got.1,?_⟩
  rw [got.2,sv.2,←FIv_NativeArray.read a index q rq]
  rfl
#print axioms zero
#print axioms value
end AspisR1.FJk_MaskValueStep
end

import NDO_JFy_SelectorInner
import NDO_JFy_SliceSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorOuter
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_copy_terminal

theorem source {N : Usize} (xs : List NQ) (iter : core.slice.iter.Iter NQ)
    (weights : Array NQ N) (len : Usize) (level : Nat)
    (hd : iter.slice.val.drop iter.i=xs) (hl : len.val=2^level)
    (cap : 2^(level+xs.length)≤N.val) (hc : FIw_ArrayValue.canonical weights)
    (hxs : ∀ x∈xs,Canon x) :
    ∃ out,Selectors.expand_loop0 iter weights len=ok out ∧ FIw_ArrayValue.canonical out := by
  induction xs generalizing iter weights len level with
  | nil =>
    have stop : ¬ (iter.i < iter.slice.val.length) := by
      have h := congrArg List.length hd
      simp only [List.length_drop,List.length_nil] at h
      omega
    refine ⟨weights,?_,hc⟩
    rw [Selectors.expand_loop0]
    simp only [core.slice.iter.IteratorSliceIter.next,Slice.len_val,stop,↓reduceDIte,bind_tc_ok]
    rfl
  | cons x xs ih =>
    have hnext := JFy_SliceSteps.slice_next_step iter x xs hd
    have hdrop := JFy_SliceSteps.slice_drop_step iter x xs hd
    have hx := hxs x (by simp)
    obtain ⟨p,hp,hvalid⟩ := FIv_PreparedNewTotal.value x hx
    have innercap : 2*len.val≤N.val := by
      have mono : 2^(level+1)≤2^(level+(x::xs).length) := Nat.pow_le_pow_right (by omega) (by simp only [List.length_cons];omega)
      rw [pow_succ] at mono
      omega
    let range : ExtractedMaskReverseRange.ReverseRange := ⟨{start:=0#usize,«end»:=len}⟩
    obtain ⟨w1,hi,hw1⟩ := JFy_SelectorInner.source len.val range weights p x hx hvalid rfl rfl innercap hc
    obtain ⟨len1,hm,hlen1⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=len) (y:=2#usize) (by scalar_tac))
    have lenval : len1.val=2^(level+1) := by
      change len1.val=len.val*2 at hlen1
      rw [pow_succ,← hl]
      exact hlen1
    obtain ⟨out,tail,hout⟩ := ih {iter with i:=iter.i+1} w1 len1 (level+1) hdrop lenval
      (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cap)
      hw1 (by intro y hy;exact hxs y (List.mem_cons_of_mem x hy))
    refine ⟨out,?_,hout⟩
    have rev : core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        ({start:=0#usize,«end»:=len} : core.ops.range.Range Usize)=ok range := rfl
    rw [Selectors.expand_loop0]
    rw [hnext,bind_tc_ok]
    change (do
      let p ← field.PreparedQm31Multiplier.new x
      let r ← core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        ({start:=0#usize,«end»:=len} : core.ops.range.Range Usize)
      let w ← Selectors.expand_loop0_loop0 r weights p
      let l ← len*2#usize
      Selectors.expand_loop0 {iter with i:=iter.i+1} w l)=ok out
    rw [hp,bind_tc_ok,rev,bind_tc_ok,hi,bind_tc_ok,hm,bind_tc_ok]
    exact tail
#print axioms source
end AspisR1.JFy_SelectorOuter
end

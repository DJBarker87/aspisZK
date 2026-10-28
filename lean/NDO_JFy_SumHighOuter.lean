import NDO_JFy_SumHighInner
import NDO_JFy_SliceSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SumHighOuter
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal
abbrev Range := core.ops.range.Range Usize

theorem source (xs : List Range) (iter : core.slice.iter.Iter Range)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (acc : field.QM31)
    (hd : iter.slice.val.drop iter.i=xs) (hb : ∀ r∈xs,r.start.val≤r.end.val ∧ r.end.val≤64)
    (hs : FIw_ArrayValue.canonical s.high) (hc : Canon acc) :
    ∃ out,sum_high_loop0 iter s acc=ok out ∧ Canon out := by
  induction xs generalizing iter acc with
  | nil =>
    have stop : ¬ (iter.i < iter.slice.val.length) := by
      have h := congrArg List.length hd
      simp only [List.length_drop,List.length_nil] at h
      omega
    refine ⟨acc,?_,hc⟩
    rw [sum_high_loop0]
    simp only [core.slice.iter.IteratorSliceIter.next,Slice.len_val,stop,↓reduceDIte,bind_tc_ok]
    rfl
  | cons r xs ih =>
    have hn := JFy_SliceSteps.slice_next_step iter r xs hd
    have ht := JFy_SliceSteps.slice_drop_step iter r xs hd
    have bounds := hb r (by simp)
    obtain ⟨a,ha,hac⟩ := JFy_SumHighInner.source (r.end.val-r.start.val) r s acc bounds.2 (by omega) hs hc
    obtain ⟨out,tail,hout⟩ := ih {iter with i:=iter.i+1} a ht
      (by intro r hr;exact hb r (List.mem_cons_of_mem _ hr)) hac
    refine ⟨out,?_,hout⟩
    rw [sum_high_loop0,hn,bind_tc_ok]
    change (do let r1 ← core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize r
               let (s1,a1) ← sum_high_loop0_loop0 r1 s acc
               sum_high_loop0 {iter with i:=iter.i+1} s1 a1)=ok out
    have clone : core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize r=ok r := rfl
    rw [clone,bind_tc_ok,ha,bind_tc_ok]
    exact tail
#print axioms source
end AspisR1.JFy_SumHighOuter
end

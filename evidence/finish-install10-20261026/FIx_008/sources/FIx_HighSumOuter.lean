import FIx_HighSumInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_HighSumOuter
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIx_HighSumInner (Selectors Range model)
abbrev Outer := pool_v1.pair_forest_semantic_terminal.sum_high_loop0
abbrev Iter := core.slice.iter.Iter Range

def ranges (rs : List Range) (s : Selectors) (acc : K) : K :=
  rs.foldl (fun a r=>model s (r.end.val-r.start.val) r.start.val a) acc

theorem next_nil (i : Iter) (done : i.slice.val.drop i.i=[]) :
    core.slice.iter.IteratorSliceIter.next i=ok (none,i) := by
  have bound : i.slice.val.length ≤ i.i := List.drop_eq_nil_iff.mp done
  simp only [core.slice.iter.IteratorSliceIter.next,Slice.len,Slice.length]
  change (if h : i.i < i.slice.val.length then ok (some (i.slice.val[i.i]),⟨i.slice,i.i+1⟩) else ok (none,i))=_
  rw [dif_neg (Nat.not_lt.mpr bound)]

theorem next_cons (i : Iter) (r : Range) (rs : List Range)
    (remaining : i.slice.val.drop i.i=r::rs) :
    ∃ next : Iter, core.slice.iter.IteratorSliceIter.next i=ok (some r,next) ∧
      next.slice.val.drop next.i=rs := by
  have bound : i.i < i.slice.val.length := by
    have : ¬ i.slice.val.drop i.i=[] := by rw [remaining];simp
    exact Nat.lt_of_not_ge (fun h=>this (List.drop_eq_nil_iff.mpr h))
  let j : Iter := ⟨i.slice,i.i+1⟩
  refine ⟨j,?_,?_⟩
  · simp only [core.slice.iter.IteratorSliceIter.next,Slice.len,Slice.length]
    change (if h : i.i < i.slice.val.length then ok (some (i.slice.val[i.i]),j) else ok (none,i))=_
    rw [dif_pos bound]
    have head : i.slice.val[i.i]'bound=r := by
      have he := congrArg (fun xs : List Range=>xs[0]?) remaining
      simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero,
        List.getElem?_eq_getElem bound,Option.some.injEq] using he
    simp only [head]
  · have he := congrArg List.tail remaining
    simpa only [List.tail_drop,List.tail_cons,j] using he

theorem value (rs : List Range) (i : Iter) (s : Selectors) (acc : NQ)
    (remaining : i.slice.val.drop i.i=rs)
    (bounds : ∀ r∈rs,r.start.val≤r.end.val ∧ r.end.val≤64)
    (hh : ∀ x∈s.high.val,Canon x) (ha : Canon acc) :
    ∃ out,Outer i s acc=ok out ∧ Canon out ∧ decode out=ranges rs s (decode acc) := by
  induction rs generalizing i acc with
  | nil =>
    refine ⟨acc,?_,ha,rfl⟩
    rw [Outer,pool_v1.pair_forest_semantic_terminal.sum_high_loop0]
    rw [next_nil i remaining,bind_tc_ok]
    rfl
  | cons r rs ih =>
    obtain ⟨j,hn,hr⟩ := next_cons i r rs remaining
    have hb := bounds r (by simp)
    obtain ⟨middle,hm,hcm,hvm⟩ := FIx_HighSumInner.value
      (r.end.val-r.start.val) r s acc hb.2 (by omega) hh ha
    obtain ⟨out,ho,hco,hvo⟩ := ih j middle hr (by intro r h;exact bounds r (by simp [h])) hcm
    refine ⟨out,?_,hco,?_⟩
    · rw [Outer,pool_v1.pair_forest_semantic_terminal.sum_high_loop0,hn,bind_tc_ok]
      have clone : core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize r=ok r := by
        cases r
        rfl
      change (do let r1 ← core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize r; let p ← pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0 r1 s acc; pool_v1.pair_forest_semantic_terminal.sum_high_loop0 j p.1 p.2)=ok out
      unfold FIx_HighSumInner.loop at hm
      rw [clone,bind_tc_ok,hm,bind_tc_ok]
      exact ho
    · rw [hvo,hvm]
      rfl

#print axioms next_nil
#print axioms next_cons
#print axioms value
end AspisR1.FIx_HighSumOuter
end

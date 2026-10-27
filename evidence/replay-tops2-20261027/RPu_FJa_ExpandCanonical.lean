import RPu_FJa_SplitCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ExpandCanonical
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
abbrev Iter := core.slice.iter.Iter NQ
/-- The installed coordinate loop preserves canonicality, for arbitrary
successful length arithmetic; the SAME slice supplies every coordinate. -/
theorem loop {N : Usize} (it : Iter) (weights out : Array NQ N) (len : Usize)
    (hc : ∀ x∈it.slice.val,Canon x) (hw : canonical weights)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 it weights len=ok out) : canonical out := by
  generalize hm : it.slice.val.length-it.i=n
  induction n using Nat.strong_induction_on generalizing it weights len with
  | h n ih =>
    rw [pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0.eq_def] at run
    by_cases more : it.i < it.slice.val.length
    · let c : NQ := it.slice[it.i]
      let next : Iter := ⟨it.slice,it.i+1⟩
      have hn : core.slice.iter.IteratorSliceIter.next it=ok (some c,next) := by
        simp [core.slice.iter.IteratorSliceIter.next,more,c,next]
        exact Aeneas.Std.Slice.getElem_Nat_eq it.slice it.i more
      rw [hn] at run
      simp only [bind_tc_ok] at run
      obtain ⟨p,hp,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨rev,hr,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨afterSplit,hs,run⟩ := FIv_Map.bind_success _ _ _ run
      obtain ⟨len1,hl,run⟩ := FIv_Map.bind_success _ _ _ run
      have hrev : rev=FJa_ReverseStep.cursor len := (Result.ok.inj hr).symm
      rw [hrev] at hs
      have cc : Canon c := by
        have eq : c=it.slice.val[it.i] := Aeneas.Std.Slice.getElem_Nat_eq it.slice it.i more
        rw [eq]
        exact hc _ (List.getElem_mem more)
      have ca := FJa_SplitCanonical.value weights afterSplit p c len cc hw hp hs
      exact ih (next.slice.val.length-next.i) (by dsimp [next];omega) next afterSplit len1 hc ca run rfl
    · have hn : core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,more]
      rw [hn] at run
      simp only [bind_tc_ok] at run
      cases Result.ok.inj run
      exact hw
#print axioms loop
end AspisR1.FJa_ExpandCanonical
end

import RPu_FJa_SplitFold
import RPu_FJa_ExpandModel
import RPu_FJa_ExpandCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_ExpandValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
abbrev Iter := core.slice.iter.Iter NQ
/-- Symbolic value of the ORIGINAL coordinate loop, on its actual iterator
suffix, with original prepared multipliers and successful arithmetic. -/
theorem loop {N : Usize} (it : Iter) (weights out : Array NQ N) (len : Usize)
    (hc : ∀ x∈it.slice.val,Canon x) (hw : canonical weights)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 it weights len=ok out) :
    FIv_NativeArray.value out=FJa_ExpandModel.value ((it.slice.val.drop it.i).map decode)
      len.val (FIv_NativeArray.value weights) := by
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
      have ce : c=it.slice.val[it.i] := Aeneas.Std.Slice.getElem_Nat_eq it.slice it.i more
      have cc : Canon c := by rw [ce]; exact hc _ (List.getElem_mem more)
      have ca := FJa_SplitCanonical.value weights afterSplit p c len cc hw hp hs
      have cv := FJa_SplitFold.value weights afterSplit p c len cc hw hp hs
      have lv : len1.val=2*len.val := by
        have h := FIw_WordValue.mul _ _ _ hl
        simpa only [show (2#usize).val=2 from rfl,Nat.mul_comm] using h
      have hvloop := ih (next.slice.val.length-next.i) (by dsimp [next];omega) next afterSplit len1 hc ca run rfl
      rw [hvloop,cv,lv]
      have suffix : it.slice.val.drop it.i=c::it.slice.val.drop (it.i+1) := by
        rw [List.drop_eq_getElem_cons more,←ce]
      rw [suffix,List.map_cons,FJa_ExpandModel.value]
    · have hn : core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,more]
      rw [hn] at run
      simp only [bind_tc_ok] at run
      cases Result.ok.inj run
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
#print axioms loop
end AspisR1.FJa_ExpandValue
end

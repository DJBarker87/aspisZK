import RPu_FJb_M31LoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_M31Loop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
abbrev Range := core.ops.range.Range Usize
/-- Symbolic traversal; each lane is updated exactly once. The same native
input arrays and accepted loop result occur in the conclusion. -/
theorem value (packed : Bool) (n : Nat) (iter : Range) (a : Constants) (state out : State)
    (hend : iter.end.val ≤ 16) (hspan : iter.start.val+n=iter.end.val)
    (ha : Bounded a) (hs : canonical state)
    (run : FJb_M31LoopStep.loop packed iter a state=ok out) :
    canonical out  ∧  ∀ j : Fin (16#usize).val, decoded out j=
      if iter.start.val ≤ j.val  ∧  j.val < iter.end.val then (decoded state j+((FJb_TailCell.cell a j).val : K))^5
      else decoded state j := by
  induction n generalizing iter state with
  | zero =>
    rw [FJb_M31LoopStep.unfold_loop packed,
      OccupancyRangeTraversal.next_done iter (by omega)] at run
    simp only [bind_tc_ok] at run
    have same : state=out := Result.ok.inj run
    subst out
    refine ⟨hs,?_⟩
    intro j
    rw [if_neg (by omega)]
  | succ n ih =>
    obtain ⟨iter1,hn,hs1,he,hb⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    rw [FJb_M31LoopStep.unfold_loop packed,hn] at run
    simp only [bind_tc_ok] at run
    obtain ⟨next,hnext,run⟩ := FIv_Map.bind_success _ _ _ run
    have hl : iter.start.val < 16 := by omega
    have vn := FJb_M31Step.value state next a iter.start hl hs ha hnext
    have vo := ih iter1 next (by rw [he];exact hend)
      (by rw [he,hs1];omega) vn.1 run
    refine ⟨vo.1,?_⟩
    intro j
    have hv := vo.2 j
    simp only [vn.2,Function.update_apply,Fin.val_mk] at hv
    by_cases hj : j.val=iter.start.val
    · have je : j=(⟨iter.start.val,hl⟩ : Fin (16#usize).val) := Fin.ext hj
      subst j
      have hf : ¬(iter1.start.val ≤ iter.start.val  ∧  iter.start.val < iter1.end.val) := by omega
      have hc : iter.start.val ≤ iter.start.val  ∧  iter.start.val < iter.end.val := by omega
      simpa only [if_neg hf,↓reduceIte,if_pos hc] using hv
    · have je : j≠(⟨iter.start.val,hl⟩ : Fin (16#usize).val) := fun h=>hj (congrArg Fin.val h)
      have hev : iter1.end.val=iter.end.val := congrArg UScalar.val he
      have heq : (iter1.start.val ≤ j.val  ∧  j.val < iter1.end.val) ↔
        (iter.start.val ≤ j.val  ∧  j.val < iter.end.val) := by omega
      simpa only [if_neg je,heq] using hv
#print axioms value
end AspisR1.FJb_M31Loop
end

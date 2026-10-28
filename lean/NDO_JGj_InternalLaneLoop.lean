import NDO_JGj_InternalLaneStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalLaneLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open JGj_RawBounds
abbrev Range := core.ops.range.Range Usize
theorem source (n : Nat) (iter : Range) (s : State) (full : Raw)
    (hl : 1 ≤ iter.start.val) (he : iter.end.val≤16) (hn : iter.start.val+n=iter.end.val)
    (hf : Bound full (62*P)) (hs : canonical s) :
    ∃ out,state_only_poseidon.internal_linear_lazy_loop1 iter s full=ok out ∧ canonical out := by
  induction n generalizing iter s with
  | zero =>
    exact ⟨s,by rw [JGj_InternalLaneStep.unfold_loop,OccupancyRangeTraversal.next_done iter (by omega),bind_tc_ok];rfl,hs⟩
  | succ n ih =>
    obtain ⟨iter1,rn,vs,ve,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨s1,rs,cs⟩ := JGj_InternalLaneStep.source s full iter.start hl (by omega) hs hf
    obtain ⟨out,ro,co⟩ := ih iter1 s1 (by omega) (by rw [ve];exact he) (by rw [ve,vs];omega) cs
    exact ⟨out,by rw [JGj_InternalLaneStep.unfold_loop,rn,bind_tc_ok];change (do let next ← JGj_InternalLaneStep.step s full iter.start;state_only_poseidon.internal_linear_lazy_loop1 iter1 next full)=ok out;rw [rs,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_InternalLaneLoop
end

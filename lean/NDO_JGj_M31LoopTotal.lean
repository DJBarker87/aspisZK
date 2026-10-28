import NDO_JGj_M31StepTotal
import RPv_FJb_M31LoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_M31LoopTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
abbrev Range := core.ops.range.Range Usize
theorem source (packed : Bool) (n : Nat) (iter : Range) (a : Constants) (s : State)
    (he : iter.end.val≤16) (hn : iter.start.val+n=iter.end.val)
    (ha : Bounded a) (hs : canonical s) :
    ∃ out,FJb_M31LoopStep.loop packed iter a s=ok out ∧ canonical out := by
  induction n generalizing iter s with
  | zero =>
    exact ⟨s,by rw [FJb_M31LoopStep.unfold_loop,OccupancyRangeTraversal.next_done iter (by omega),bind_tc_ok];rfl,hs⟩
  | succ n ih =>
    obtain ⟨iter1,rn,vs,ve,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨s1,rs,cs⟩ := JGj_M31StepTotal.source s a iter.start (by change iter.start.val<16;omega) hs ha
    obtain ⟨out,ro,co⟩ := ih iter1 s1 (by rw [ve];exact he) (by rw [ve,vs];omega) cs
    exact ⟨out,by rw [FJb_M31LoopStep.unfold_loop,rn,bind_tc_ok];change (do let next ← FJb_M31Step.step s a iter.start;FJb_M31LoopStep.loop packed iter1 a next)=ok out;rw [rs,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_M31LoopTotal
end

import NDO_JGj_QmStepTotal
import RPv_FJb_QmRoundStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_QmLoopTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_QmRoundStep (State)
abbrev Range := core.ops.range.Range Usize
theorem source (packed : Bool) (n : Nat) (iter : Range) (a : State) (s : State)
    (he : iter.end.val≤16) (hn : iter.start.val+n=iter.end.val)
    (ha : canonical a) (hs : canonical s) :
    ∃ out,FJb_QmRoundStep.loop packed iter a s=ok out ∧ canonical out := by
  induction n generalizing iter s with
  | zero =>
    exact ⟨s,by rw [FJb_QmRoundStep.unfold_loop,OccupancyRangeTraversal.next_done iter (by omega),bind_tc_ok];rfl,hs⟩
  | succ n ih =>
    obtain ⟨iter1,rn,vs,ve,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨s1,rs,cs⟩ := JGj_QmStepTotal.source a s iter.start (by omega) ha hs
    obtain ⟨out,ro,co⟩ := ih iter1 s1 (by rw [ve];exact he) (by rw [ve,vs];omega) cs
    exact ⟨out,by rw [FJb_QmRoundStep.unfold_loop,rn,bind_tc_ok];change (do let next ← FJb_QmRoundStep.step a s iter.start;FJb_QmRoundStep.loop packed iter1 a next)=ok out;rw [rs,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_QmLoopTotal
end

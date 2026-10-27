import RPu_FIy_FrontierLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.FIy_FrontierFrame
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIy_FrontierStep (Snapshot Selectors)
open FIy_FrontierLoopStep (loop)
abbrev Range := core.ops.range.Range Usize

theorem value (n : Nat) (r : Range) (a : Array NQ 16#usize) (s : Selectors)
    (d out : Array NQ 8#usize) (src returned : Snapshot)
    (span : r.start.val+n=r.end.val)
    (success : loop r a s d src=ok (out,returned)) : returned=src := by
  induction n generalizing r d with
  | zero=>
    rw [FIy_FrontierLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok] at success
    exact (Prod.mk.inj (Result.ok.inj success)).2.symm
  | succ n ih=>
    obtain ⟨r',hn,hstart,he,hbound⟩ := OccupancyRangeTraversal.next_step r (by omega)
    rw [FIy_FrontierLoopStep.value,hn,bind_tc_ok] at success
    change (do let next←FIy_FrontierStep.run r.start a s d src;loop r' a s next src)=ok (out,returned) at success
    obtain ⟨next,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    exact ih r' next (by rw [he];omega) tail
#print axioms value
end AspisR1.FIy_FrontierFrame

import XSc_AccumulateCuts
import XSc_PushLoopFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_AccumulateFrame
/-- This actual query's complete pending row loop fixes both counter and raw
shape; the checked increment is the sole term-counter update. -/
theorem source (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (pending after : verifier.BatchedWeights)
 (run : verifier.accumulate_batched_with_node p a node value pending=ok (out,after)) :
 after.raw.val.length=pending.raw.val.length ∧
 (pending.terms+1#usize : Result Usize)=ok after.terms := by
 obtain ⟨one,basis,rows,_,hr,ht,_,_,_,hf⟩ :=
  XSc_AccumulateCuts.source p a out node value pending after run
 have frame := XSc_PushLoopFrame.source a.weights a.power a.next
  (alloc.vec.Vec.len a.weights) basis _ pending rows hr
 refine ⟨?_,?_⟩
 · rw [hf]; exact frame.1
 · rw [←frame.2]; exact ht
#print axioms source
end XSc_AccumulateFrame

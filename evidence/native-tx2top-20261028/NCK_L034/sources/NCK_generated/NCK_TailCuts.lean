import VTop_SecondFlow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_TailCuts
open Aeneas Aeneas.Std Result VTop_Stages
/-- Exactly the relation-only view constructed after the query loop. -/
def view (inactive : aspis_core.field.wide_exact.WideExact)
    (round0 round1 finalMessage : Slice U8) : verifier.View :=
  {variant := .S2,semantic := (Std.Array.empty U8).to_slice,
   y1 := (Std.Array.empty U8).to_slice,inactive,round0,folded_root := none,
   round1,final_message := finalMessage,query_bytes := (Std.Array.empty U8).to_slice}
/-- The native top caller retains rhs/power/next while replacing only weights
with the SAME pending.finish reply through the emitted Vec lens. -/
def flushed (a : verifier.Accumulator)
    (weights : Slice aspis_core.field.wide_exact.WideExact) : verifier.Accumulator :=
  {a with weights := (alloc.vec.Vec.deref_mut a.weights).2 weights}
/-- Actual model tail composition, including the Vec lens and final view.
The finish equation remains a U13 model cut, not a native bridge. -/
theorem compose (ops : VTop_Stages.Ops) (proof : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights)
    (inactive : aspis_core.field.wide_exact.WideExact)
    (round0 folded round1 finalOffset openingOffset : Usize)
    (round0Bytes round1Bytes finalBytes : Slice U8)
    (weights : Slice aspis_core.field.wide_exact.WideExact)
    (flushCut : ops.op9 pending a.weights.deref = ok weights)
    (round0Range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := round0, «end» := folded} = ok round0Bytes)
    (finalCut : ops.op21 = ok finalOffset)
    (round1Range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := round1, «end» := finalOffset} = ok round1Bytes)
    (openingCut : ops.op20 = ok openingOffset)
    (finalRange : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := finalOffset, «end» := openingOffset} = ok finalBytes)
    (finishCut : ops.op19 (view inactive round0Bytes round1Bytes finalBytes)
      p (flushed a weights) none = ok (.Ok ())) :
    VTop_SecondFlow.tail (VTop_Flow.sourceEffects ops) proof p none inactive
      round0 folded round1 (a,pending) = ok (.Ok ()) := by
  change (do
    let updated ← ops.op9 pending a.weights.deref
    let r0 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := round0, «end» := folded}
    let f ← ops.op21
    let r1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := round1, «end» := f}
    let o ← ops.op20
    let finalBytes' ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := f, «end» := o}
    ops.op19 (view inactive r0 r1 finalBytes') p (flushed a updated) none) = _
  simp only [flushCut, round0Range, finalCut, round1Range, openingCut, finalRange,
    finishCut, bind_tc_ok]
#print axioms compose
end AspisR1.NCK_TailCuts
end

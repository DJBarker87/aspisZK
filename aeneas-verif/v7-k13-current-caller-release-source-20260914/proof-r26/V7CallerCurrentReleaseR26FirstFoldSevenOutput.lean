import V7CallerCurrentReleaseR26FirstFoldSevenSource

/-!
# Exact post-first-fold component vector

The traversal theorem exposes each of the seven output cells separately.  This
file packages those cells as the exact returned vector used by the following
multilinear merge.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26FirstFoldSevenOutput

open V7CallerCurrentReleaseR26WeightFoldLoopTrace
open V7CallerCurrentReleaseR26FirstFoldSevenSource

abbrev RawM31 := field.M31
abbrev RawQM31 := field.QM31

theorem FirstFoldSevenSourceTrace.folded_components_exact
    {input output : sumcheck.WeightAccumulator} {alpha : RawQM31}
    {trace : FirstDeferredFoldTrace input alpha output}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {alpha0 : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec RawM31}
    (source : FirstFoldSevenSourceTrace input alpha output trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs) :
    trace.foldedComponents.val =
      [.Multilinear source.mScale0Out source.mPoint0Out,
       .Multilinear source.mScale1Out source.mPoint1Out,
       .Multilinear source.mScale2Out source.mPoint2Out,
       .Grouped64x16BinaryDeferred source.rowGroupsOut source.groupMasksOut
         source.firstAlphaOut source.groupValuesOut,
       .Tensor source.tScale0Out source.tFactors0Out,
       .Tensor source.tScale1Out source.tFactors1Out,
       .LineM31Batch
         ((alloc.vec.Vec.deref_mut lineScales).2 source.lineScalesSliceOut)
         ((alloc.vec.Vec.deref_mut lineXs).2 source.lineXsSliceOut)
         source.lineDeferredOut] := by
  apply List.ext_getElem
  · simpa using source.outputLength
  · intro index leftBound rightBound
    rw [List.Inhabited_getElem_eq_getElem!
      trace.foldedComponents.val index leftBound]
    have indexBound : index < 7 := by simpa using rightBound
    interval_cases index
    · simpa only [List.getElem_cons_zero] using source.cell0
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell1
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell2
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell3
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell4
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell5
    · simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using
        source.cell6

theorem FirstFoldSevenSourceTrace.output_components_exact
    {input output : sumcheck.WeightAccumulator} {alpha : RawQM31}
    {trace : FirstDeferredFoldTrace input alpha output}
    {mScale0 mScale1 mScale2 : RawQM31}
    {mPoint0 mPoint1 mPoint2 : alloc.vec.Vec RawQM31}
    {alpha0 : RawQM31} {groupValues : alloc.vec.Vec RawQM31}
    {tScale0 tScale1 : RawQM31}
    {tFactors0 tFactors1 : alloc.vec.Vec RawQM31}
    {lineScales : alloc.vec.Vec RawQM31}
    {lineXs : alloc.vec.Vec RawM31}
    (source : FirstFoldSevenSourceTrace input alpha output trace
      mScale0 mScale1 mScale2 mPoint0 mPoint1 mPoint2 alpha0 groupValues
      tScale0 tScale1 tFactors0 tFactors1 lineScales lineXs) :
    output.components.val =
      [.Multilinear source.mScale0Out source.mPoint0Out,
       .Multilinear source.mScale1Out source.mPoint1Out,
       .Multilinear source.mScale2Out source.mPoint2Out,
       .Grouped64x16BinaryDeferred source.rowGroupsOut source.groupMasksOut
         source.firstAlphaOut source.groupValuesOut,
       .Tensor source.tScale0Out source.tFactors0Out,
       .Tensor source.tScale1Out source.tFactors1Out,
       .LineM31Batch
         ((alloc.vec.Vec.deref_mut lineScales).2 source.lineScalesSliceOut)
         ((alloc.vec.Vec.deref_mut lineXs).2 source.lineXsSliceOut)
         source.lineDeferredOut] := by
  rw [trace.outputComponents]
  exact V7CallerCurrentReleaseR26FirstFoldSevenOutput.FirstFoldSevenSourceTrace.folded_components_exact
    source

#print axioms FirstFoldSevenSourceTrace.folded_components_exact
#print axioms FirstFoldSevenSourceTrace.output_components_exact

end V7CallerCurrentReleaseR26FirstFoldSevenOutput

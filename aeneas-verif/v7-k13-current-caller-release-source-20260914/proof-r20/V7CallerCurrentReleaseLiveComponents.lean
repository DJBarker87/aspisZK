import V7CallerCurrentReleaseTensorLoop
import V7CallerCurrentReleaseMultilinearLoop
import V7CallerCurrentReleaseGroupedBinaryLog8

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseLiveComponents

open V7CallerCurrentReleaseFieldBridge

abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
/-- The current generated component dispatcher consumes a live multilinear
    component through the verified indexed multilinear loop. -/
theorem generated_live_multilinear_component_corresponds
    (scale : QM31) (point : alloc.vec.Vec QM31) (index : Std.U32)
    (hWidth : (alloc.vec.Vec.deref point).length ≤ 32)
    (hScale : GeneratedCanonicalQM31 scale)
    (hCanonical :
      V7CallerCurrentReleaseMultilinearLoop.CanonicalSlice
        (alloc.vec.Vec.deref point)) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
        8#u32 (V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Multilinear scale point) index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix scale
            (alloc.vec.Vec.deref point) index
            (alloc.vec.Vec.deref point).length ⦄ := by
  simpa only [
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed]
    using V7CallerCurrentReleaseMultilinearLoop.generated_multilinear_loop_corresponds
      scale (alloc.vec.Vec.deref point) index hWidth hScale hCanonical

/-- The current generated component dispatcher consumes a live tensor
    component through the verified indexed tensor loop. -/
theorem generated_live_tensor_component_corresponds
    (scale : QM31) (factors : alloc.vec.Vec QM31) (index : Std.U32)
    (hWidth : (alloc.vec.Vec.deref factors).length ≤ 32)
    (hScale : GeneratedCanonicalQM31 scale)
    (hCanonical :
      V7CallerCurrentReleaseTensorLoop.CanonicalSlice
        (alloc.vec.Vec.deref factors)) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
        8#u32 (V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Tensor scale factors) index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          V7CallerCurrentReleaseTensorLoop.tensorPrefix scale
            (alloc.vec.Vec.deref factors) index
            (alloc.vec.Vec.deref factors).length ⦄ := by
  simpa only [
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed]
    using V7CallerCurrentReleaseTensorLoop.generated_tensor_loop_corresponds
      scale (alloc.vec.Vec.deref factors) index hWidth hScale hCanonical

/-- The current generated component dispatcher selects the log-eight branch
    of the deferred grouped-binary evaluator and preserves its exact decoded
    fourfold equation. -/
theorem generated_live_grouped_component_corresponds
    (rowGroups : alloc.vec.Vec Std.U8) (groupMasks : alloc.vec.Vec Std.U16)
    (alpha : QM31) (groupValues : alloc.vec.Vec QM31) (index : Std.U32)
    (hIndex : index.val < 256)
    (hRows : (alloc.vec.Vec.deref rowGroups).length = 64)
    (hGroup : ∀ row, row < 64 →
      (alloc.vec.Vec.deref rowGroups).val[row]!.val <
        (alloc.vec.Vec.deref groupMasks).length)
    (hAlpha : GeneratedCanonicalQM31 alpha) :
    ∃ out,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
          8#u32
          (V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Grouped64x16BinaryDeferred rowGroups groupMasks
            (some alpha) groupValues) index = ok out ∧
      GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out + generatedQm31ToExact out +
          generatedQm31ToExact out + generatedQm31ToExact out =
        V7CallerCurrentReleaseGroupedBinaryLog8.rawNibbleSum
          (generatedQm31ToExact alpha)
          (V7CallerCurrentReleaseGroupedBinaryLog8.sourceBits
            (alloc.vec.Vec.deref groupMasks).val[
              (alloc.vec.Vec.deref rowGroups).val[index.val / 4]!.val]!
            index) := by
  obtain ⟨out, hrun, hcanonical, hexact⟩ :=
    V7CallerCurrentReleaseGroupedBinaryLog8.generated_grouped_log8_corresponds
      (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupMasks)
      alpha index hIndex hRows hGroup hAlpha
  refine ⟨out, ?_, hcanonical, hexact⟩
  unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
  change
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_indexed
        8#u32 (alloc.vec.Vec.deref rowGroups)
        (alloc.vec.Vec.deref groupMasks) (some alpha)
        (alloc.vec.Vec.deref groupValues) index = ok out
  unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_indexed
  change
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_grouped_binary_deferred_log8
        (alloc.vec.Vec.deref rowGroups) (alloc.vec.Vec.deref groupMasks)
        (some alpha) index = ok out
  exact hrun

#print axioms generated_live_multilinear_component_corresponds
#print axioms generated_live_tensor_component_corresponds
#print axioms generated_live_grouped_component_corresponds

end V7CallerCurrentReleaseLiveComponents

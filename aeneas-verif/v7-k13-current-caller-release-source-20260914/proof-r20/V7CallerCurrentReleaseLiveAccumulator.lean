import V7CallerCurrentReleaseAccumulatorLoop

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseLiveAccumulator

open V7CallerCurrentReleaseFieldBridge
open V7CallerCurrentReleaseAccumulatorLoop

abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31
abbrev Component := V7CallerCurrentReleaseR20.sumcheck.WeightComponent
abbrev Accumulator := V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator

private def liveSemantic
    (m0 m1 m2 grouped t0 t1 : ExactQM31) (componentIndex : Nat) : ExactQM31 :=
  match componentIndex with
  | 0 => m0
  | 1 => m1
  | 2 => m2
  | 3 => grouped
  | 4 => t0
  | 5 => t1
  | _ => 0

/-- Exact current-source `weight_at` refinement for the literal post-round-zero
    Tag-73 shape: three multilinears, one deferred grouped-binary component,
    and two tensor components at log length eight. -/
theorem generated_live_six_component_accumulator_corresponds
    (self : Accumulator) (index : Std.U32)
    (mScale0 mScale1 mScale2 : QM31)
    (mPoint0 mPoint1 mPoint2 : alloc.vec.Vec QM31)
    (rowGroups : alloc.vec.Vec Std.U8) (groupMasks : alloc.vec.Vec Std.U16)
    (alpha : QM31) (groupValues : alloc.vec.Vec QM31)
    (tScale0 tScale1 : QM31)
    (tFactors0 tFactors1 : alloc.vec.Vec QM31)
    (hLog : self.log_len = 8#u32)
    (hComponents : self.components.val =
      [V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Multilinear mScale0 mPoint0,
       V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Multilinear mScale1 mPoint1,
       V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Multilinear mScale2 mPoint2,
       V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Grouped64x16BinaryDeferred rowGroups groupMasks
         (some alpha) groupValues,
       V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Tensor tScale0 tFactors0,
       V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Tensor tScale1 tFactors1])
    (hIndex : index.val < 256)
    (hMWidth0 : (alloc.vec.Vec.deref mPoint0).length ≤ 32)
    (hMWidth1 : (alloc.vec.Vec.deref mPoint1).length ≤ 32)
    (hMWidth2 : (alloc.vec.Vec.deref mPoint2).length ≤ 32)
    (hTWidth0 : (alloc.vec.Vec.deref tFactors0).length ≤ 32)
    (hTWidth1 : (alloc.vec.Vec.deref tFactors1).length ≤ 32)
    (hMScale0 : GeneratedCanonicalQM31 mScale0)
    (hMScale1 : GeneratedCanonicalQM31 mScale1)
    (hMScale2 : GeneratedCanonicalQM31 mScale2)
    (hTScale0 : GeneratedCanonicalQM31 tScale0)
    (hTScale1 : GeneratedCanonicalQM31 tScale1)
    (hAlpha : GeneratedCanonicalQM31 alpha)
    (hMCanonical0 : V7CallerCurrentReleaseMultilinearLoop.CanonicalSlice
      (alloc.vec.Vec.deref mPoint0))
    (hMCanonical1 : V7CallerCurrentReleaseMultilinearLoop.CanonicalSlice
      (alloc.vec.Vec.deref mPoint1))
    (hMCanonical2 : V7CallerCurrentReleaseMultilinearLoop.CanonicalSlice
      (alloc.vec.Vec.deref mPoint2))
    (hTCanonical0 : V7CallerCurrentReleaseTensorLoop.CanonicalSlice
      (alloc.vec.Vec.deref tFactors0))
    (hTCanonical1 : V7CallerCurrentReleaseTensorLoop.CanonicalSlice
      (alloc.vec.Vec.deref tFactors1))
    (hRows : (alloc.vec.Vec.deref rowGroups).length = 64)
    (hGroup : ∀ row, row < 64 →
      (alloc.vec.Vec.deref rowGroups).val[row]!.val <
        (alloc.vec.Vec.deref groupMasks).length) :
    ∃ groupedRaw out,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at self index = ok out ∧
      GeneratedCanonicalQM31 groupedRaw ∧ GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact groupedRaw + generatedQm31ToExact groupedRaw +
          generatedQm31ToExact groupedRaw + generatedQm31ToExact groupedRaw =
        V7CallerCurrentReleaseGroupedBinaryLog8.rawNibbleSum
          (generatedQm31ToExact alpha)
          (V7CallerCurrentReleaseGroupedBinaryLog8.sourceBits
            (alloc.vec.Vec.deref groupMasks).val[
              (alloc.vec.Vec.deref rowGroups).val[index.val / 4]!.val]!
            index) ∧
      generatedQm31ToExact out =
        V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale0
            (alloc.vec.Vec.deref mPoint0) index
            (alloc.vec.Vec.deref mPoint0).length +
        V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale1
            (alloc.vec.Vec.deref mPoint1) index
            (alloc.vec.Vec.deref mPoint1).length +
        V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale2
            (alloc.vec.Vec.deref mPoint2) index
            (alloc.vec.Vec.deref mPoint2).length +
        generatedQm31ToExact groupedRaw +
        V7CallerCurrentReleaseTensorLoop.tensorPrefix tScale0
            (alloc.vec.Vec.deref tFactors0) index
            (alloc.vec.Vec.deref tFactors0).length +
        V7CallerCurrentReleaseTensorLoop.tensorPrefix tScale1
            (alloc.vec.Vec.deref tFactors1) index
            (alloc.vec.Vec.deref tFactors1).length := by
  obtain ⟨groupedRaw, hGroupedRun, hGroupedCanonical, hGroupedExact⟩ :=
    V7CallerCurrentReleaseLiveComponents.generated_live_grouped_component_corresponds
      rowGroups groupMasks alpha groupValues index hIndex hRows hGroup hAlpha
  let m0 := V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale0
    (alloc.vec.Vec.deref mPoint0) index (alloc.vec.Vec.deref mPoint0).length
  let m1 := V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale1
    (alloc.vec.Vec.deref mPoint1) index (alloc.vec.Vec.deref mPoint1).length
  let m2 := V7CallerCurrentReleaseMultilinearLoop.multilinearPrefix mScale2
    (alloc.vec.Vec.deref mPoint2) index (alloc.vec.Vec.deref mPoint2).length
  let t0 := V7CallerCurrentReleaseTensorLoop.tensorPrefix tScale0
    (alloc.vec.Vec.deref tFactors0) index (alloc.vec.Vec.deref tFactors0).length
  let t1 := V7CallerCurrentReleaseTensorLoop.tensorPrefix tScale1
    (alloc.vec.Vec.deref tFactors1) index (alloc.vec.Vec.deref tFactors1).length
  let semantic := liveSemantic m0 m1 m2 (generatedQm31ToExact groupedRaw) t0 t1
  have hLength : self.components.length = 6 := by simpa [hComponents]
  have hRuns : ∀ componentIndex,
      componentIndex < self.components.length →
      ComponentRun self.log_len index self.components.val[componentIndex]!
        (semantic componentIndex) := by
    intro componentIndex hBound
    rw [hLength] at hBound
    have hCases : componentIndex = 0 ∨ componentIndex = 1 ∨
        componentIndex = 2 ∨ componentIndex = 3 ∨ componentIndex = 4 ∨
        componentIndex = 5 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨raw, hrun, hcanonical, hexact⟩ := Aeneas.Std.WP.spec_imp_exists
        (V7CallerCurrentReleaseLiveComponents.generated_live_multilinear_component_corresponds
          mScale0 mPoint0 index hMWidth0 hMScale0 hMCanonical0)
      exact ⟨raw, by simpa [ComponentRun, hLog, hComponents, semantic,
        liveSemantic, m0] using hrun, hcanonical, by simpa [semantic,
        liveSemantic, m0] using hexact⟩
    · obtain ⟨raw, hrun, hcanonical, hexact⟩ := Aeneas.Std.WP.spec_imp_exists
        (V7CallerCurrentReleaseLiveComponents.generated_live_multilinear_component_corresponds
          mScale1 mPoint1 index hMWidth1 hMScale1 hMCanonical1)
      exact ⟨raw, by simpa [ComponentRun, hLog, hComponents, semantic,
        liveSemantic, m1] using hrun, hcanonical, by simpa [semantic,
        liveSemantic, m1] using hexact⟩
    · obtain ⟨raw, hrun, hcanonical, hexact⟩ := Aeneas.Std.WP.spec_imp_exists
        (V7CallerCurrentReleaseLiveComponents.generated_live_multilinear_component_corresponds
          mScale2 mPoint2 index hMWidth2 hMScale2 hMCanonical2)
      exact ⟨raw, by simpa [ComponentRun, hLog, hComponents, semantic,
        liveSemantic, m2] using hrun, hcanonical, by simpa [semantic,
        liveSemantic, m2] using hexact⟩
    · exact ⟨groupedRaw, by simpa [ComponentRun, hLog, hComponents] using hGroupedRun,
        hGroupedCanonical, by simp [semantic, liveSemantic]⟩
    · obtain ⟨raw, hrun, hcanonical, hexact⟩ := Aeneas.Std.WP.spec_imp_exists
        (V7CallerCurrentReleaseLiveComponents.generated_live_tensor_component_corresponds
          tScale0 tFactors0 index hTWidth0 hTScale0 hTCanonical0)
      exact ⟨raw, by simpa [ComponentRun, hLog, hComponents, semantic,
        liveSemantic, t0] using hrun, hcanonical, by simpa [semantic,
        liveSemantic, t0] using hexact⟩
    · obtain ⟨raw, hrun, hcanonical, hexact⟩ := Aeneas.Std.WP.spec_imp_exists
        (V7CallerCurrentReleaseLiveComponents.generated_live_tensor_component_corresponds
          tScale1 tFactors1 index hTWidth1 hTScale1 hTCanonical1)
      exact ⟨raw, by simpa [ComponentRun, hLog, hComponents, semantic,
        liveSemantic, t1] using hrun, hcanonical, by simpa [semantic,
        liveSemantic, t1] using hexact⟩
  obtain ⟨out, hOutRun, hOutCanonical, hOutExact⟩ := Aeneas.Std.WP.spec_imp_exists
    (generated_accumulator_loop_corresponds self index semantic hRuns)
  refine ⟨groupedRaw, out, hOutRun, hGroupedCanonical, hOutCanonical,
    hGroupedExact, ?_⟩
  rw [hOutExact, hLength]
  simp [exactPrefix, Finset.sum_range_succ, semantic, liveSemantic,
    m0, m1, m2, t0, t1]

#print axioms generated_live_six_component_accumulator_corresponds

end V7CallerCurrentReleaseLiveAccumulator

import V7CallerCurrentReleaseR26Qm31DotRawInnerLoop

/-!
# One active input of the generated raw QM31-dot loop

This connects the production slice reads and QM31 component pairing to the
complete three-component inner-loop proof.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawOuterBody

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26Qm31DotInnerIterator
open V7CallerCurrentReleaseR26Qm31DotRawInnerLoop

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev Pair := CM31 × CM31
abbrev Raw := Array Std.U64 9#usize

local instance : Inhabited Std.U64 := ⟨0#u64⟩
local instance : Inhabited QM31 := ⟨field.QM31.ZERO⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩

def RawUniversalHeadroom (raw : Raw) : Prop :=
  ∀ lane, lane < 9 → ∀ left right : M31,
    GeneratedCanonicalM31 left → GeneratedCanonicalM31 right →
    raw.val[lane]!.val + rawM31Product left right < 2 ^ 64

private theorem slice_index_run
    {T : Type} [Inhabited T] (values : Slice T) (index : Std.Usize)
    (bound : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

/-- One active source-body iteration performs the exact nine raw-lane updates
for `(c0,c0)`, `(c1,c1)`, and `(c0+c1,c0+c1)`. -/
theorem generated_raw_outer_body_active
    (weights values : Slice QM31)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (index : Std.Usize) (raw : Raw)
    (iteratorRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some index, nextIter))
    (weightBound : index.val < weights.length)
    (valueBound : index.val < values.length)
    (weightCanonical :
      GeneratedCanonicalQM31 weights.val[index.val]!)
    (valueCanonical :
      GeneratedCanonicalQM31 values.val[index.val]!)
    (headroom : RawUniversalHeadroom raw) :
    ∃ weightSum valueSum rawNext,
      field.qm31_dot_loop0_loop0.body weights values iter raw =
        ok (cont (nextIter, rawNext)) ∧
      field.CM31.add weights.val[index.val]!.c0
          weights.val[index.val]!.c1 = ok weightSum ∧
      field.CM31.add values.val[index.val]!.c0
          values.val[index.val]!.c1 = ok valueSum ∧
      GeneratedCanonicalCM31 weightSum ∧
      GeneratedCanonicalCM31 valueSum ∧
      generatedCm31ToExact weightSum =
        generatedCm31ToExact weights.val[index.val]!.c0 +
          generatedCm31ToExact weights.val[index.val]!.c1 ∧
      generatedCm31ToExact valueSum =
        generatedCm31ToExact values.val[index.val]!.c0 +
          generatedCm31ToExact values.val[index.val]!.c1 ∧
      let pairs : Array Pair 3#usize := Array.make 3#usize [
        (weights.val[index.val]!.c0, values.val[index.val]!.c0),
        (weights.val[index.val]!.c1, values.val[index.val]!.c1),
        (weightSum, valueSum)]
      ∀ component, component < 3 →
        ExactRawComponentStep raw rawNext component pairs.val[component]! := by
  let weight := weights.val[index.val]!
  let value := values.val[index.val]!
  have weightRead : Slice.index_usize weights index = ok weight :=
    slice_index_run weights index weightBound
  have valueRead : Slice.index_usize values index = ok value :=
    slice_index_run values index valueBound
  obtain ⟨weightSum, weightSumRun, weightSumCanonical, weightSumExact⟩ :=
    generated_cm31_add_corresponds weight.c0 weight.c1
      weightCanonical.1 weightCanonical.2
  obtain ⟨valueSum, valueSumRun, valueSumCanonical, valueSumExact⟩ :=
    generated_cm31_add_corresponds value.c0 value.c1
      valueCanonical.1 valueCanonical.2
  let pairs : Array Pair 3#usize := Array.make 3#usize [
    (weight.c0, value.c0), (weight.c1, value.c1), (weightSum, valueSum)]
  have pairs0 : pairs.val[0]! = (weight.c0, value.c0) := by
    rfl
  have pairs1 : pairs.val[1]! = (weight.c1, value.c1) := by
    rfl
  have pairs2 : pairs.val[2]! = (weightSum, valueSum) := by
    rfl
  have pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2 := by
    intro component componentBound
    have componentCases : component = 0 ∨ component = 1 ∨ component = 2 := by
      omega
    rcases componentCases with rfl | rfl | rfl
    · rw [pairs0]
      exact And.intro weightCanonical.1 valueCanonical.1
    · rw [pairs1]
      exact And.intro weightCanonical.2 valueCanonical.2
    · rw [pairs2]
      exact And.intro weightSumCanonical valueSumCanonical
  have componentBounds : ∀ component, component < 3 →
      RawComponentBounds raw component pairs.val[component]! := by
    intro component componentBound
    unfold RawComponentBounds
    refine ⟨headroom (component * 3) (by omega) _ _
        (pairsCanonical component componentBound).1.1
        (pairsCanonical component componentBound).2.1, ?_, ?_⟩
    · exact headroom (component * 3 + 1) (by omega) _ _
        (pairsCanonical component componentBound).1.2
        (pairsCanonical component componentBound).2.2
    · exact headroom (component * 3 + 2) (by omega) _ _
        (canonicalM31Sum_spec _ _
          (pairsCanonical component componentBound).1.1
          (pairsCanonical component componentBound).1.2).2.1
        (canonicalM31Sum_spec _ _
          (pairsCanonical component componentBound).2.1
          (pairsCanonical component componentBound).2.2).2.1
  have iteratorInitial := generated_pair_iterator_initial pairs
  have innerRun := generated_raw_inner_loop_exact pairs raw pairsCanonical
  have innerExact := raw_after_components_three_corresponds pairs raw
    pairsCanonical componentBounds
  refine ⟨weightSum, valueSum, rawAfterComponents pairs raw 3,
    ?_, weightSumRun, valueSumRun, weightSumCanonical, valueSumCanonical,
    weightSumExact, valueSumExact, ?_⟩
  · unfold field.qm31_dot_loop0_loop0.body
    rw [iteratorRun]
    simp only [bind_tc_ok]
    rw [weightRead, valueRead]
    simp only [bind_tc_ok]
    rw [weightSumRun, valueSumRun]
    simp only [bind_tc_ok]
    change
      (do
        let iter2 ←
          (do
            let into ←
              Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
                pairs
            core.iter.traits.iterator.Iterator.enumerate.trait_default
              (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
                Pair 3#usize) into)
        let raw2 ← field.qm31_dot_loop0_loop0_loop0 iter2 raw
        ok (cont (nextIter, raw2))) = _
    rw [iteratorInitial]
    simp only [bind_tc_ok]
    rw [innerRun]
    simp
  · simpa [pairs, weight, value] using innerExact

#print axioms generated_raw_outer_body_active

end V7CallerCurrentReleaseR26Qm31DotRawOuterBody

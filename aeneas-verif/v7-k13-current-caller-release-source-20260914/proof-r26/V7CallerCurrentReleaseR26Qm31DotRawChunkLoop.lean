import V7CallerCurrentReleaseR26Qm31DotRawOuterBody

/-!
# Four-input raw chunk invariant

Each raw chunk contains at most four products per lane.  The invariant below
turns that count into the headroom premise used by the verified outer body.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotRawChunkLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26Qm31DotRawArithmetic
open V7CallerCurrentReleaseR26Qm31DotRawInnerLoop
open V7CallerCurrentReleaseR26Qm31DotRawOuterBody

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev Pair := CM31 × CM31
abbrev Raw := Array Std.U64 9#usize
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31

local instance : Inhabited Std.U64 := ⟨0#u64⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩
local instance : Inhabited QM31 := ⟨field.QM31.ZERO⟩

theorem generated_input_pairs_canonical
    (weight value : QM31)
    (weightCanonical : GeneratedCanonicalQM31 weight)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    ∀ component, component < 3 →
      GeneratedCanonicalCM31
          (generatedInputPairs weight value).val[component]!.1 ∧
        GeneratedCanonicalCM31
          (generatedInputPairs weight value).val[component]!.2 := by
  let pairs := generatedInputPairs weight value
  have pairs0 : pairs.val[0]! = (weight.c0, value.c0) := by rfl
  have pairs1 : pairs.val[1]! = (weight.c1, value.c1) := by rfl
  have pairs2 : pairs.val[2]! =
      (⟨canonicalM31Sum weight.c0.a weight.c1.a,
          canonicalM31Sum weight.c0.b weight.c1.b⟩,
       ⟨canonicalM31Sum value.c0.a value.c1.a,
          canonicalM31Sum value.c0.b value.c1.b⟩) := by rfl
  change ∀ component, component < 3 →
    GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
      GeneratedCanonicalCM31 pairs.val[component]!.2
  intro component componentBound
  have weightSumA := canonicalM31Sum_spec weight.c0.a weight.c1.a
    weightCanonical.1.1 weightCanonical.2.1
  have weightSumB := canonicalM31Sum_spec weight.c0.b weight.c1.b
    weightCanonical.1.2 weightCanonical.2.2
  have valueSumA := canonicalM31Sum_spec value.c0.a value.c1.a
    valueCanonical.1.1 valueCanonical.2.1
  have valueSumB := canonicalM31Sum_spec value.c0.b value.c1.b
    valueCanonical.1.2 valueCanonical.2.2
  have componentCases : component = 0 ∨ component = 1 ∨ component = 2 := by
    omega
  rcases componentCases with rfl | rfl | rfl
  · rw [pairs0]
    exact And.intro weightCanonical.1 valueCanonical.1
  · rw [pairs1]
    exact And.intro weightCanonical.2 valueCanonical.2
  · rw [pairs2]
    exact And.intro (And.intro weightSumA.2.1 weightSumB.2.1)
      (And.intro valueSumA.2.1 valueSumB.2.1)

def exactPairLane0 (pair : Pair) : ExactM31 :=
  generatedM31ToExact pair.1.a * generatedM31ToExact pair.2.a

def exactPairLane1 (pair : Pair) : ExactM31 :=
  generatedM31ToExact pair.1.b * generatedM31ToExact pair.2.b

def exactPairLane2 (pair : Pair) : ExactM31 :=
  (generatedM31ToExact pair.1.a + generatedM31ToExact pair.1.b) *
    (generatedM31ToExact pair.2.a + generatedM31ToExact pair.2.b)

def ExactRawChunkPrefix
    (weights values : Slice QM31) (start processed : Nat) (raw : Raw) : Prop :=
  ∀ component, component < 3 →
    let pairAt := fun offset =>
      (generatedInputPairs weights.val[start + offset]!
        values.val[start + offset]!).val[component]!
    (raw.val[component * 3]!.val : ExactM31) =
        ∑ offset ∈ Finset.range processed, exactPairLane0 (pairAt offset) ∧
      (raw.val[component * 3 + 1]!.val : ExactM31) =
        ∑ offset ∈ Finset.range processed, exactPairLane1 (pairAt offset) ∧
      (raw.val[component * 3 + 2]!.val : ExactM31) =
        ∑ offset ∈ Finset.range processed, exactPairLane2 (pairAt offset)

theorem exact_component_steps_advance_prefix
    (weights values : Slice QM31) (start processed : Nat)
    (before after : Raw)
    (beforeExact : ExactRawChunkPrefix weights values start processed before)
    (steps : ∀ component, component < 3 →
      ExactRawComponentStep before after component
        (generatedInputPairs weights.val[start + processed]!
          values.val[start + processed]!).val[component]!) :
    ExactRawChunkPrefix weights values start (processed + 1) after := by
  intro component componentBound
  have prior := beforeExact component componentBound
  have step := steps component componentBound
  unfold ExactRawComponentStep at step
  dsimp only at prior ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [step.1, prior.1]
    simp [exactPairLane0, Finset.sum_range_succ]
  · rw [step.2.1, prior.2.1]
    simp [exactPairLane1, Finset.sum_range_succ]
  · rw [step.2.2, prior.2.2]
    simp [exactPairLane2, Finset.sum_range_succ]

def RawComponentCountBound (raw : Raw) (processed : Nat) : Prop :=
  ∀ component, component < 3 →
    raw.val[component * 3]!.val ≤ processed * 2 ^ 62 ∧
      raw.val[component * 3 + 1]!.val ≤ processed * 2 ^ 62 ∧
      raw.val[component * 3 + 2]!.val ≤ processed * 2 ^ 62

theorem raw_component_count_bound_headroom
    (raw : Raw) (processed : Nat)
    (processedBound : processed < 4)
    (bound : RawComponentCountBound raw processed) :
    RawUniversalHeadroom raw := by
  intro lane laneBound left right leftCanonical rightCanonical
  have productBound := canonical_m31_product_lt_two_pow_62 left right
    leftCanonical rightCanonical
  have laneCases : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3 ∨
      lane = 4 ∨ lane = 5 ∨ lane = 6 ∨ lane = 7 ∨ lane = 8 := by
    omega
  rcases laneCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have current := (bound 0 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 0 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 0 (by omega)).2.2
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 1 (by omega)).2.2
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).1
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).2.1
    norm_num at current ⊢
    omega
  · have current := (bound 2 (by omega)).2.2
    norm_num at current ⊢
    omega

theorem natural_component_steps_advance_count_bound
    (before after : Raw) (processed : Nat) (pairs : Array Pair 3#usize)
    (beforeBound : RawComponentCountBound before processed)
    (pairsCanonical : ∀ component, component < 3 →
      GeneratedCanonicalCM31 pairs.val[component]!.1 ∧
        GeneratedCanonicalCM31 pairs.val[component]!.2)
    (steps : ∀ component, component < 3 →
      NaturalRawComponentStep before after component pairs.val[component]!) :
    RawComponentCountBound after (processed + 1) := by
  intro component componentBound
  have prior := beforeBound component componentBound
  have canonical := pairsCanonical component componentBound
  have step := steps component componentBound
  have product0 := canonical_m31_product_lt_two_pow_62
    pairs.val[component]!.1.a pairs.val[component]!.2.a
      canonical.1.1 canonical.2.1
  have product1 := canonical_m31_product_lt_two_pow_62
    pairs.val[component]!.1.b pairs.val[component]!.2.b
      canonical.1.2 canonical.2.2
  have leftSumSpec := canonicalM31Sum_spec pairs.val[component]!.1.a
    pairs.val[component]!.1.b canonical.1.1 canonical.1.2
  have rightSumSpec := canonicalM31Sum_spec pairs.val[component]!.2.a
    pairs.val[component]!.2.b canonical.2.1 canonical.2.2
  have product2 := canonical_m31_product_lt_two_pow_62
    (canonicalM31Sum pairs.val[component]!.1.a
      pairs.val[component]!.1.b)
    (canonicalM31Sum pairs.val[component]!.2.a
      pairs.val[component]!.2.b)
    leftSumSpec.2.1 rightSumSpec.2.1
  unfold NaturalRawComponentStep at step
  refine ⟨?_, ?_, ?_⟩
  · rw [step.1]
    omega
  · rw [step.2.1]
    omega
  · rw [step.2.2]
    omega

def RawChunkInvariant
    (weights values : Slice QM31) (start processed : Nat) (raw : Raw) : Prop :=
  ExactRawChunkPrefix weights values start processed raw ∧
    RawComponentCountBound raw processed

theorem generated_raw_chunk_body_active
    (weights values : Slice QM31)
    (iter nextIter : core.ops.range.Range Std.Usize)
    (index : Std.Usize) (raw : Raw) (start processed : Nat)
    (iteratorRun :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        ok (some index, nextIter))
    (indexExact : index.val = start + processed)
    (processedBound : processed < 4)
    (weightBound : index.val < weights.length)
    (valueBound : index.val < values.length)
    (weightCanonical : GeneratedCanonicalQM31 weights.val[index.val]!)
    (valueCanonical : GeneratedCanonicalQM31 values.val[index.val]!)
    (invariant : RawChunkInvariant weights values start processed raw) :
    ∃ rawNext,
      field.qm31_dot_loop0_loop0.body weights values iter raw =
        ok (cont (nextIter, rawNext)) ∧
      RawChunkInvariant weights values start (processed + 1) rawNext := by
  have headroom := raw_component_count_bound_headroom raw processed
    processedBound invariant.2
  obtain ⟨rawNext, bodyRun, steps⟩ :=
    generated_raw_outer_body_active_canonical weights values iter nextIter
      index raw iteratorRun weightBound valueBound weightCanonical
      valueCanonical headroom
  let pairs := generatedInputPairs weights.val[index.val]!
    values.val[index.val]!
  have pairsCanonical := generated_input_pairs_canonical
    weights.val[index.val]! values.val[index.val]!
      weightCanonical valueCanonical
  have exactSteps : ∀ component, component < 3 →
      ExactRawComponentStep raw rawNext component
        (generatedInputPairs weights.val[start + processed]!
          values.val[start + processed]!).val[component]! := by
    intro component componentBound
    simpa [indexExact] using (steps component componentBound).1
  have naturalSteps : ∀ component, component < 3 →
      NaturalRawComponentStep raw rawNext component pairs.val[component]! := by
    intro component componentBound
    exact (steps component componentBound).2
  refine ⟨rawNext, bodyRun, ?_, ?_⟩
  · exact exact_component_steps_advance_prefix weights values start processed
      raw rawNext invariant.1 exactSteps
  · exact natural_component_steps_advance_count_bound raw rawNext
      processed pairs invariant.2 pairsCanonical naturalSteps

/-- A range of exactly four inputs completes with the exact four-input raw
prefix and the corresponding no-wrap count bound. -/
theorem generated_raw_chunk_loop_four
    (weights values : Slice QM31)
    (iter : core.ops.range.Range Std.Usize) (raw : Raw) (start : Nat)
    (startExact : iter.start.val = start)
    (endExact : iter.end.val = start + 4)
    (weightLength : start + 4 ≤ weights.length)
    (valueLength : start + 4 ≤ values.length)
    (weightsCanonical : ∀ offset, offset < 4 →
      GeneratedCanonicalQM31 weights.val[start + offset]!)
    (valuesCanonical : ∀ offset, offset < 4 →
      GeneratedCanonicalQM31 values.val[start + offset]!)
    (initial : RawChunkInvariant weights values start 0 raw) :
    field.qm31_dot_loop0_loop0 iter weights values raw
      ⦃ out => RawChunkInvariant weights values start 4 out ⦄ := by
  unfold field.qm31_dot_loop0_loop0
  apply loop.spec_decr_nat
    (fun state : core.ops.range.Range Std.Usize × Raw =>
      start + 4 - state.1.start.val)
    (fun state => ∃ processed, processed ≤ 4 ∧
      state.1.start.val = start + processed ∧
      state.1.end.val = start + 4 ∧
      RawChunkInvariant weights values start processed state.2)
    (fun out => RawChunkInvariant weights values start 4 out)
  · rintro ⟨currentIter, currentRaw⟩
      ⟨processed, processedBound, currentStart, currentEnd,
        currentInvariant⟩
    dsimp only at currentStart currentEnd currentInvariant ⊢
    by_cases active : processed < 4
    · have iteratorActive : currentIter.start.val < currentIter.end.val := by
        omega
      obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact,
          nextStart, nextEnd⟩ := Aeneas.Std.WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec currentIter
          iteratorActive)
      rw [optionExact] at iteratorRun
      let index := currentIter.start
      have indexRun :
          core.iter.range.IteratorRange.next core.iter.range.StepUsize
              currentIter = ok (some index, nextIter) := by
        simpa [index] using iteratorRun
      have indexExact : index.val = start + processed := by
        simpa [index] using currentStart
      have weightBound : index.val < weights.length := by omega
      have valueBound : index.val < values.length := by omega
      have weightCanonical : GeneratedCanonicalQM31
          weights.val[index.val]! := by
        simpa [indexExact] using weightsCanonical processed active
      have valueCanonical : GeneratedCanonicalQM31
          values.val[index.val]! := by
        simpa [indexExact] using valuesCanonical processed active
      obtain ⟨rawNext, bodyRun, nextInvariant⟩ :=
        generated_raw_chunk_body_active weights values currentIter nextIter
          index currentRaw start processed indexRun indexExact active
          weightBound valueBound weightCanonical valueCanonical
          currentInvariant
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨processed + 1, by omega, ?_, ?_, nextInvariant⟩, ?_⟩
      · rw [nextStart, currentStart]
        omega
      · rw [nextEnd, currentEnd]
      · rw [nextStart, currentStart]
        omega
    · have finished : processed = 4 := by omega
      subst processed
      have iteratorFinished : currentIter.end.val ≤ currentIter.start.val := by
        omega
      obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact,
          _nextExact⟩ := Aeneas.Std.WP.spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_none_spec currentIter
          iteratorFinished)
      rw [optionExact] at iteratorRun
      unfold field.qm31_dot_loop0_loop0.body
      rw [iteratorRun]
      simpa using currentInvariant
  · exact ⟨0, by omega, startExact, endExact, initial⟩

#print axioms raw_component_count_bound_headroom
#print axioms natural_component_steps_advance_count_bound
#print axioms generated_input_pairs_canonical
#print axioms exact_component_steps_advance_prefix
#print axioms generated_raw_chunk_body_active
#print axioms generated_raw_chunk_loop_four

end V7CallerCurrentReleaseR26Qm31DotRawChunkLoop

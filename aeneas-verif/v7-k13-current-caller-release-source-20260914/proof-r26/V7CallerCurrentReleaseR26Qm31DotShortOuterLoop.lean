import V7CallerCurrentReleaseR26Qm31DotChunkReduction

/-!
# Exact short-path outer loop for the current optimized QM31 dot product

The production short path visits sixteen inputs in four chunks of four.  This
file lifts the verified four-input chunk to that complete `step_by(4)` loop.
-/

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26Qm31DotShortOuterLoop

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26Qm31DotReconstruction
open V7CallerCurrentReleaseR26Qm31DotRawOuterBody
open V7CallerCurrentReleaseR26Qm31DotRawInnerLoop
open V7CallerCurrentReleaseR26Qm31DotRawChunkLoop
open V7CallerCurrentReleaseR26Qm31DotReductionLoop
open V7CallerCurrentReleaseR26Qm31DotChunkReduction

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31

local instance : Inhabited M31 := ⟨field.M31.ZERO⟩
local instance : Inhabited CM31 :=
  ⟨{ a := field.M31.ZERO, b := field.M31.ZERO }⟩
local instance : Inhabited QM31 := ⟨field.QM31.ZERO⟩

def ExactReducedPrefix
    (weights values : Slice QM31) (processed : Nat)
    (sums : Array M31 9#usize) : Prop :=
  CanonicalDotChannels sums ∧
    ∀ component, component < 3 →
      let pairAt := fun input =>
        (generatedInputPairs weights.val[input]!
          values.val[input]!).val[component]!
      generatedM31ToExact sums.val[component * 3]! =
          ∑ input ∈ Finset.range processed, exactPairLane0 (pairAt input) ∧
        generatedM31ToExact sums.val[component * 3 + 1]! =
          ∑ input ∈ Finset.range processed, exactPairLane1 (pairAt input) ∧
        generatedM31ToExact sums.val[component * 3 + 2]! =
          ∑ input ∈ Finset.range processed, exactPairLane2 (pairAt input)

theorem reduced_chunk_advances_exact_prefix
    (weights values : Slice QM31) (start : Nat)
    (base out : Array M31 9#usize)
    (baseExact : ExactReducedPrefix weights values start base)
    (chunkExact : ReducedChunkPrefix weights values start base out) :
    ExactReducedPrefix weights values (start + 4) out := by
  constructor
  · exact chunkExact.1
  · intro component componentBound
    have baseComponent := baseExact.2 component componentBound
    have chunkComponent := chunkExact.2 component componentBound
    dsimp only at baseComponent chunkComponent ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [chunkComponent.1, baseComponent.1, Finset.sum_range_add]
    · rw [chunkComponent.2.1, baseComponent.2.1, Finset.sum_range_add]
    · rw [chunkComponent.2.2, baseComponent.2.2, Finset.sum_range_add]

theorem zero_channels_exact_prefix
    (weights values : Slice QM31) :
    ExactReducedPrefix weights values 0
      (Array.repeat 9#usize field.M31.ZERO) := by
  constructor
  · intro channel channelBound
    have channelCases : channel = 0 ∨ channel = 1 ∨ channel = 2 ∨
        channel = 3 ∨ channel = 4 ∨ channel = 5 ∨ channel = 6 ∨
        channel = 7 ∨ channel = 8 := by omega
    rcases channelCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [GeneratedCanonicalM31,
      AspisAeneasCM31Multiplicative.CanonicalRawM31,
      field.M31.ZERO]
  · intro component componentBound
    have componentCases : component = 0 ∨ component = 1 ∨ component = 2 := by
      omega
    rcases componentCases with rfl | rfl | rfl <;>
      norm_num [generatedM31ToExact, field.M31.ZERO]

private theorem wrapping_add_four_small
    (start : Std.Usize) (bound : start.val + 4 < Usize.size) :
    (Std.Usize.wrapping_add start 4#usize).val = start.val + 4 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  exact Nat.mod_eq_of_lt bound

theorem generated_short_outer_body_active
    (weights values : Slice QM31)
    (iter : core.iter.adapters.step_by.StepBy
      (core.ops.range.Range Std.Usize))
    (sums : Array M31 9#usize) (start : Nat)
    (startExact : iter.iter.start.val = start)
    (endExact : iter.iter.end.val = 16)
    (stepExact : iter.step_by.val = 4)
    (active : start < 16)
    (wholeChunk : start + 4 ≤ 16)
    (weightLength : weights.length = 16)
    (valueLength : values.length = 16)
    (weightsCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 weights.val[input]!)
    (valuesCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 values.val[input]!)
    (initialExact : ExactReducedPrefix weights values start sums) :
    field.qm31_dot_loop0.body weights values iter sums
      ⦃ flow => ∃ nextIter nextSums,
        flow = cont (nextIter, nextSums) ∧
        nextIter.iter.start.val = start + 4 ∧
        nextIter.iter.end.val = 16 ∧
        nextIter.step_by.val = 4 ∧
        ExactReducedPrefix weights values (start + 4) nextSums ⦄ := by
  have iteratorActive : iter.iter.start.val < iter.iter.end.val := by omega
  have iteratorStep : 0 < iter.step_by.val := by omega
  have iteratorStepInRange :
      iter.iter.start.val + iter.step_by.val ≤ iter.iter.end.val := by omega
  obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact,
      nextStart, nextEnd, nextStep⟩ := Aeneas.Std.WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec
      iter iteratorActive iteratorStep iteratorStepInRange)
  rw [optionExact] at iteratorRun
  let chunkStart := iter.iter.start
  have chunkStartExact : chunkStart.val = start := by
    simpa [chunkStart] using startExact
  let chunkEnd := Std.Usize.wrapping_add chunkStart 4#usize
  have usizeBound : start + 4 < Usize.size := by
    have literalBound := UScalar.hSize (16#usize)
    have : 16 < Usize.size := by
      simpa [UScalar.size_UScalarTyUsize] using literalBound
    omega
  have chunkEndExact : chunkEnd.val = start + 4 := by
    dsimp [chunkEnd]
    rw [wrapping_add_four_small chunkStart (by simpa [chunkStartExact])]
    exact chunkStartExact ▸ rfl
  have minRun :
      core.cmp.min core.cmp.OrdUsize chunkEnd (Slice.len weights) =
        ok chunkEnd := by
    simp [core.cmp.min,
      core.cmp.impls.OrdUsize.min, chunkEndExact, weightLength]
    intro nearEnd
    apply UScalar.eq_of_val_eq
    simp [weightLength, chunkEndExact]
    omega
  have rawSpec := generated_raw_chunk_loop_four weights values
    { start := chunkStart, «end» := chunkEnd }
    (Array.repeat 9#usize 0#u64) start chunkStartExact chunkEndExact
    (by omega) (by omega)
    (by
      intro offset offsetBound
      apply weightsCanonical
      omega)
    (by
      intro offset offsetBound
      apply valuesCanonical
      omega)
    (zero_raw_chunk_initial weights values start)
  obtain ⟨raw, rawRun, rawInvariant⟩ :=
    Aeneas.Std.WP.spec_imp_exists rawSpec
  have reducedSpec :=
    generated_dot_reduction_all_channels sums raw initialExact.1
  obtain ⟨nextSums, nextSumsRun, nextSumsExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists reducedSpec
  have chunkExact : ReducedChunkPrefix weights values start sums nextSums := by
    constructor
    · exact nextSumsExact.1
    · intro component componentBound
      have rawExact := rawInvariant.1 component componentBound
      dsimp only at rawExact ⊢
      have reduced0 := nextSumsExact.2 (component * 3) (by omega)
      have reduced1 := nextSumsExact.2 (component * 3 + 1) (by omega)
      have reduced2 := nextSumsExact.2 (component * 3 + 2) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [reduced0, rawExact.1]
      · rw [reduced1, rawExact.2.1]
      · rw [reduced2, rawExact.2.2]
  unfold field.qm31_dot_loop0.body
  rw [iteratorRun]
  simp only [bind_tc_ok]
  change
    (do
      let i ← lift (Std.Usize.wrapping_add chunkStart 4#usize)
      let i1 := Slice.len weights
      let end1 ← core.cmp.min core.cmp.OrdUsize i i1
      let raw1 := Array.repeat 9#usize 0#u64
      let raw2 ← field.qm31_dot_loop0_loop0
        { start := chunkStart, «end» := end1 } weights values raw1
      let sums1 ← field.qm31_dot_loop0_loop1
        { start := 0#usize, «end» := 9#usize } sums raw2
      ok (cont (nextIter, sums1))) ⦃ flow => _ ⦄
  simp only [Std.lift, bind_tc_ok]
  rw [show Std.Usize.wrapping_add chunkStart 4#usize = chunkEnd by rfl]
  rw [minRun]
  simp only [bind_tc_ok]
  rw [rawRun]
  simp only [bind_tc_ok]
  rw [nextSumsRun]
  refine ⟨nextIter, nextSums, rfl, ?_, ?_, ?_, ?_⟩
  · rw [nextStart, startExact, stepExact]
  · simpa [endExact] using congrArg UScalar.val nextEnd
  · simpa [stepExact] using congrArg UScalar.val nextStep
  · exact reduced_chunk_advances_exact_prefix weights values start sums
      nextSums initialExact chunkExact

theorem generated_short_outer_loop_sixteen
    (weights values : Slice QM31)
    (iter : core.iter.adapters.step_by.StepBy
      (core.ops.range.Range Std.Usize))
    (sums : Array M31 9#usize)
    (startExact : iter.iter.start.val = 0)
    (endExact : iter.iter.end.val = 16)
    (stepExact : iter.step_by.val = 4)
    (weightLength : weights.length = 16)
    (valueLength : values.length = 16)
    (weightsCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 weights.val[input]!)
    (valuesCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 values.val[input]!)
    (initialExact : ExactReducedPrefix weights values 0 sums) :
    field.qm31_dot_loop0 iter weights values sums
      ⦃ out => ExactReducedPrefix weights values 16 out ⦄ := by
  unfold field.qm31_dot_loop0
  apply loop.spec_decr_nat
    (fun state :
        (core.iter.adapters.step_by.StepBy
          (core.ops.range.Range Std.Usize)) × (Array M31 9#usize) =>
      4 - state.1.iter.start.val / 4)
    (fun state => ∃ chunks, chunks ≤ 4 ∧
      state.1.iter.start.val = chunks * 4 ∧
      state.1.iter.end.val = 16 ∧
      state.1.step_by.val = 4 ∧
      ExactReducedPrefix weights values (chunks * 4) state.2)
    (fun out => ExactReducedPrefix weights values 16 out)
  · rintro ⟨currentIter, currentSums⟩
      ⟨chunks, chunksBound, currentStart, currentEnd, currentStep,
        currentExact⟩
    dsimp only at currentStart currentEnd currentStep currentExact ⊢
    by_cases active : chunks < 4
    · have processedBound : chunks * 4 + 4 ≤ 16 := by omega
      have bodySpec := generated_short_outer_body_active weights values
        currentIter currentSums (chunks * 4) currentStart currentEnd
        currentStep (by omega) processedBound weightLength valueLength
        weightsCanonical valuesCanonical currentExact
      obtain ⟨flow, bodyRun, nextIter, nextSums, flowExact,
          nextStart, nextEnd, nextStep, nextExact⟩ :=
        Aeneas.Std.WP.spec_imp_exists bodySpec
      rw [flowExact] at bodyRun
      rw [bodyRun]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨chunks + 1, by omega, ?_, nextEnd, nextStep, ?_⟩, ?_⟩
      · omega
      · convert nextExact using 1
        all_goals omega
      · rw [nextStart]
        omega
    · have finished : chunks = 4 := by omega
      subst chunks
      have iteratorFinished :
          currentIter.iter.start.val ≥ currentIter.iter.end.val := by omega
      obtain ⟨⟨option, nextIter⟩, iteratorRun, optionExact,
          nextExact⟩ := Aeneas.Std.WP.spec_imp_exists
        (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec
          currentIter iteratorFinished)
      rw [optionExact] at iteratorRun
      unfold field.qm31_dot_loop0.body
      rw [iteratorRun]
      simpa using currentExact
  · exact ⟨0, by omega, startExact, endExact, stepExact, initialExact⟩

theorem exact_dot_component_from_prefix
    (weights values : Slice QM31) (processed component : Nat)
    (sums : Array M31 9#usize)
    (componentBound : component < 3)
    (exact : ExactReducedPrefix weights values processed sums) :
    exactDotComponent sums (component * 3) =
      ∑ input ∈ Finset.range processed,
        let pair := (generatedInputPairs weights.val[input]!
          values.val[input]!).val[component]!
        generatedCm31ToExact pair.1 * generatedCm31ToExact pair.2 := by
  have componentExact := exact.2 component componentBound
  let pairAt := fun (input : Nat) =>
    (generatedInputPairs weights.val[input]!
      values.val[input]!).val[component]!
  let productAt := fun (input : Nat) =>
    generatedCm31ToExact (pairAt input).1 *
      generatedCm31ToExact (pairAt input).2
  have productSumReal : ∀ inputs : Finset Nat,
      (∑ input ∈ inputs, productAt input).re =
        ∑ input ∈ inputs,
          (exactPairLane0 (pairAt input) - exactPairLane1 (pairAt input)) := by
    intro inputs
    induction inputs using Finset.induction_on with
    | empty => simp
    | @insert input inputs inputFresh ih =>
        simp only [Finset.sum_insert inputFresh]
        change (productAt input).re +
          (∑ input ∈ inputs, productAt input).re = _
        rw [ih]
        simp [productAt, pairAt, exactPairLane0, exactPairLane1,
          generatedCm31ToExact, generatedM31ToExact]
        ring
  have productSumImag : ∀ inputs : Finset Nat,
      (∑ input ∈ inputs, productAt input).im =
        ∑ input ∈ inputs,
          (exactPairLane2 (pairAt input) - exactPairLane0 (pairAt input) -
            exactPairLane1 (pairAt input)) := by
    intro inputs
    induction inputs using Finset.induction_on with
    | empty => simp
    | @insert input inputs inputFresh ih =>
        simp only [Finset.sum_insert inputFresh]
        change (productAt input).im +
          (∑ input ∈ inputs, productAt input).im = _
        rw [ih]
        simp [productAt, pairAt, exactPairLane0,
          exactPairLane1, exactPairLane2, generatedCm31ToExact,
          generatedM31ToExact]
        ring
  dsimp only at componentExact ⊢
  unfold exactDotComponent
  rw [componentExact.1, componentExact.2.1, componentExact.2.2]
  apply QuadraticAlgebra.ext
  · rw [show
        (∑ input ∈ Finset.range processed,
          generatedCm31ToExact (pairAt input).1 *
            generatedCm31ToExact (pairAt input).2).re = _ from
        productSumReal (Finset.range processed)]
    rw [Finset.sum_sub_distrib]
  · rw [show
        (∑ input ∈ Finset.range processed,
          generatedCm31ToExact (pairAt input).1 *
            generatedCm31ToExact (pairAt input).2).im = _ from
        productSumImag (Finset.range processed)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

theorem generated_input_channels_reconstruct_product
    (weight value : QM31)
    (weightCanonical : GeneratedCanonicalQM31 weight)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    let pairs : Array (CM31 × CM31) 3#usize :=
      generatedInputPairs weight value
    let productAt := fun (component : Nat) =>
      generatedCm31ToExact pairs.val[component]!.1 *
        generatedCm31ToExact pairs.val[component]!.2
    (⟨productAt 0 + productAt 1 * exactQm31R,
        productAt 2 - productAt 0 - productAt 1⟩ :
          V7CallerCurrentReleaseR26FieldBridge.ExactQM31) =
      generatedQm31ToExact weight * generatedQm31ToExact value := by
  have weightSumA := canonicalM31Sum_spec weight.c0.a weight.c1.a
    weightCanonical.1.1 weightCanonical.2.1
  have weightSumB := canonicalM31Sum_spec weight.c0.b weight.c1.b
    weightCanonical.1.2 weightCanonical.2.2
  have valueSumA := canonicalM31Sum_spec value.c0.a value.c1.a
    valueCanonical.1.1 valueCanonical.2.1
  have valueSumB := canonicalM31Sum_spec value.c0.b value.c1.b
    valueCanonical.1.2 valueCanonical.2.2
  have weightSumExact :
      generatedCm31ToExact
          ⟨canonicalM31Sum weight.c0.a weight.c1.a,
            canonicalM31Sum weight.c0.b weight.c1.b⟩ =
        generatedCm31ToExact weight.c0 + generatedCm31ToExact weight.c1 := by
    apply QuadraticAlgebra.ext
    · exact weightSumA.2.2
    · exact weightSumB.2.2
  have valueSumExact :
      generatedCm31ToExact
          ⟨canonicalM31Sum value.c0.a value.c1.a,
            canonicalM31Sum value.c0.b value.c1.b⟩ =
        generatedCm31ToExact value.c0 + generatedCm31ToExact value.c1 := by
    apply QuadraticAlgebra.ext
    · exact valueSumA.2.2
    · exact valueSumB.2.2
  have pairs0 : (generatedInputPairs weight value).val[0]! =
      (weight.c0, value.c0) := by rfl
  have pairs1 : (generatedInputPairs weight value).val[1]! =
      (weight.c1, value.c1) := by rfl
  have pairs2 : (generatedInputPairs weight value).val[2]! =
      (⟨canonicalM31Sum weight.c0.a weight.c1.a,
          canonicalM31Sum weight.c0.b weight.c1.b⟩,
       ⟨canonicalM31Sum value.c0.a value.c1.a,
          canonicalM31Sum value.c0.b value.c1.b⟩) := by rfl
  dsimp only
  rw [pairs0, pairs1, pairs2, weightSumExact, valueSumExact]
  apply QuadraticAlgebra.ext
  · simp [generatedQm31ToExact]
    ring
  · simp [generatedQm31ToExact]
    ring

theorem exact_reconstruction_from_prefix
    (weights values : Slice QM31) (processed : Nat)
    (sums : Array M31 9#usize)
    (weightsCanonical : ∀ input, input < processed →
      GeneratedCanonicalQM31 weights.val[input]!)
    (valuesCanonical : ∀ input, input < processed →
      GeneratedCanonicalQM31 values.val[input]!)
    (exact : ExactReducedPrefix weights values processed sums) :
    exactQm31FromDotChannels sums =
      ∑ input ∈ Finset.range processed,
        generatedQm31ToExact weights.val[input]! *
          generatedQm31ToExact values.val[input]! := by
  let pairAt := fun (input component : Nat) =>
    (generatedInputPairs weights.val[input]!
      values.val[input]!).val[component]!
  let productAt := fun (input component : Nat) =>
    generatedCm31ToExact (pairAt input component).1 *
      generatedCm31ToExact (pairAt input component).2
  have component0 := exact_dot_component_from_prefix weights values processed
    0 sums (by omega) exact
  have component1 := exact_dot_component_from_prefix weights values processed
    1 sums (by omega) exact
  have component2 := exact_dot_component_from_prefix weights values processed
    2 sums (by omega) exact
  have component0Exact : exactDotComponent sums 0 =
      ∑ input ∈ Finset.range processed, productAt input 0 := by
    simpa [pairAt, productAt] using component0
  have component1Exact : exactDotComponent sums 3 =
      ∑ input ∈ Finset.range processed, productAt input 1 := by
    simpa [pairAt, productAt] using component1
  have component2Exact : exactDotComponent sums 6 =
      ∑ input ∈ Finset.range processed, productAt input 2 := by
    simpa [pairAt, productAt] using component2
  have aggregate : ∀ inputs : Finset Nat,
      (∀ input ∈ inputs, input < processed) →
      (⟨(∑ input ∈ inputs, productAt input 0) +
            (∑ input ∈ inputs, productAt input 1) * exactQm31R,
          (∑ input ∈ inputs, productAt input 2) -
            (∑ input ∈ inputs, productAt input 0) -
            (∑ input ∈ inputs, productAt input 1)⟩ :
          V7CallerCurrentReleaseR26FieldBridge.ExactQM31) =
        ∑ input ∈ inputs,
          generatedQm31ToExact weights.val[input]! *
            generatedQm31ToExact values.val[input]! := by
    intro inputs inputsBound
    induction inputs using Finset.induction_on with
    | empty =>
        apply QuadraticAlgebra.ext <;> simp
    | @insert input inputs inputFresh ih =>
        have inputBound : input < processed :=
          inputsBound input (by simp)
        have remainingBound : ∀ index ∈ inputs, index < processed := by
          intro index indexMem
          exact inputsBound index (by simp [indexMem])
        have inputExact := generated_input_channels_reconstruct_product
          weights.val[input]! values.val[input]!
          (weightsCanonical input inputBound)
          (valuesCanonical input inputBound)
        have inputExact' :
            (⟨productAt input 0 + productAt input 1 * exactQm31R,
                productAt input 2 - productAt input 0 - productAt input 1⟩ :
              V7CallerCurrentReleaseR26FieldBridge.ExactQM31) =
            generatedQm31ToExact weights.val[input]! *
              generatedQm31ToExact values.val[input]! := by
          simpa [pairAt, productAt] using inputExact
        have remainingExact := ih remainingBound
        simp only [Finset.sum_insert inputFresh]
        rw [← inputExact', ← remainingExact]
        apply QuadraticAlgebra.ext <;> simp <;> ring
  unfold exactQm31FromDotChannels
  rw [component0Exact, component1Exact, component2Exact]
  exact aggregate (Finset.range processed) (by
    intro input inputMem
    simpa using inputMem)

/-- End-to-end exact semantics for the production short path at its release
boundary of sixteen inputs. -/
theorem generated_qm31_dot_sixteen_corresponds
    (weights values : Slice QM31)
    (weightLength : weights.length = 16)
    (valueLength : values.length = 16)
    (weightsCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 weights.val[input]!)
    (valuesCanonical : ∀ input, input < 16 →
      GeneratedCanonicalQM31 values.val[input]!) :
    ∃ out,
      field.qm31_dot weights values = ok out ∧
      GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          ∑ input ∈ Finset.range 16,
            generatedQm31ToExact weights.val[input]! *
              generatedQm31ToExact values.val[input]! := by
  have weightLengthScalar : Slice.len weights = 16#usize := by
    apply UScalar.eq_of_val_eq
    simpa using weightLength
  have valueLengthScalar : Slice.len values = 16#usize := by
    apply UScalar.eq_of_val_eq
    simpa using valueLength
  have iteratorSpec :=
    core.iter.traits.iterator.Iterator.step_by.trait_default.spec
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      ({ start := 0#usize, «end» := 16#usize } :
        core.ops.range.Range Std.Usize)
      4#usize (by norm_num)
  obtain ⟨iter, iteratorRun, iterBase, iterStep⟩ :=
    Aeneas.Std.WP.spec_imp_exists iteratorSpec
  have iterStart : iter.iter.start.val = 0 := by
    rw [iterBase]
    norm_num
  have iterEnd : iter.iter.end.val = 16 := by
    rw [iterBase]
    norm_num
  have iterStepExact : iter.step_by.val = 4 := by
    rw [iterStep]
    norm_num
  have loopSpec := generated_short_outer_loop_sixteen weights values iter
    (Array.repeat 9#usize field.M31.ZERO) iterStart iterEnd iterStepExact
    weightLength valueLength weightsCanonical valuesCanonical
    (zero_channels_exact_prefix weights values)
  obtain ⟨sums, loopRun, sumsExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists loopSpec
  have reconstructionSpec :=
    generated_dot_reconstruction_corresponds sums sumsExact.1
  obtain ⟨out, reconstructionRun, outCanonical, outExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists reconstructionSpec
  have reconstructedExact := exact_reconstruction_from_prefix weights values
    16 sums weightsCanonical valuesCanonical sumsExact
  refine ⟨out, ?_, outCanonical, outExact.trans reconstructedExact⟩
  unfold field.qm31_dot
  rw [weightLengthScalar, valueLengthScalar]
  dsimp only
  rw [show massert ((16#usize : Std.Usize) = 16#usize) = ok () by
    simp [massert]]
  simp only [bind_tc_ok]
  rw [if_pos (by rfl)]
  rw [iteratorRun]
  simp only [bind_tc_ok]
  rw [loopRun]
  simp only [bind_tc_ok]
  exact reconstructionRun

#print axioms reduced_chunk_advances_exact_prefix
#print axioms zero_channels_exact_prefix
#print axioms generated_short_outer_body_active
#print axioms generated_short_outer_loop_sixteen
#print axioms exact_dot_component_from_prefix
#print axioms generated_input_channels_reconstruct_product
#print axioms exact_reconstruction_from_prefix
#print axioms generated_qm31_dot_sixteen_corresponds

end V7CallerCurrentReleaseR26Qm31DotShortOuterLoop

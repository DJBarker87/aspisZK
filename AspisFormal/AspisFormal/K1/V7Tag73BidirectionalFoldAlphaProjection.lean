import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaController
import AspisFormal.K1.V7Tag73AlphaZeroProducerInvariant

/-!
# Alpha-state projection of the bidirectional fold controller

After the unique fold-nonce boundary, the bidirectional wrapper and the
standalone alpha-zero controller perform the same producer and used-slot
transition.  The only extra wrapper branch consumes the 41-byte fold-work
input; that input cannot be a 33-byte alpha squeeze coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73BidirectionalFoldAlphaProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A current input whose length is not 33 cannot be selected as an alpha
squeeze output by any producer inventory. -/
theorem alpha_zero_preferred_none_of_input_length_ne
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (input : ShaInput)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (lengthNe : input.length ≠ 33) :
    alphaZeroPreferredSlot transitionFuel state = none := by
  cases preferred : alphaZeroPreferredSlot transitionFuel state with
  | none => rfl
  | some slot =>
      obtain ⟨selectedInput, producer, selectedInputExact, _member,
          selectedOutput, _block⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel state slot
          preferred
      have selectedEq : selectedInput = input :=
        Option.some.inj (selectedInputExact.symm.trans inputExact)
      apply (lengthNe _).elim
      rw [← selectedEq, selectedOutput]
      simp [bytes_length]

@[simp] theorem literal_fold_work_length
    (digest : Digest256) (nonce : NonceBytes) :
    (bytes digest ++ domGrind :: bytes nonce).length = 41 := by
  simp [bytes_length]

/-- Away from the unique boundary ordinal and boundary input, the dynamic
fold-armed alpha layer projects exactly to the standalone alpha transition. -/
theorem fold_armed_alpha_projects_to_alpha_zero_after_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256)
    (indexNe : state.exposureIndex ≠ boundaryIndex)
    (boundaryNe : state.memory.expectedBoundary ≠
      unifiedInputBeforeAnswer? transitionFuel state.cursor) :
    (foldArmedAlphaAfterMemory transitionFuel state answer).alpha =
      alphaZeroAfterMemory transitionFuel boundaryIndex
        (foldArmedAlphaIndexedState state) answer := by
  unfold foldArmedAlphaAfterMemory alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simp [inputExact, foldArmedAlphaIndexedState]
  | some input =>
      have expectedNe : state.memory.expectedBoundary ≠ some input := by
        simpa [inputExact] using boundaryNe
      simp [foldArmedAlphaIndexedState, inputExact, expectedNe, indexNe]
      rfl

/-- The wrapper's exceptional work-consumption branch also has the same alpha
projection, because the exact work input cannot consume an alpha slot. -/
theorem bidirectional_alpha_projects_to_alpha_zero_after_boundary
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) (workInput : ShaInput)
    (afterAnchor : state.exposureIndex ≠ anchorIndex)
    (afterBoundary : state.exposureIndex ≠ boundaryIndex)
    (expectedBoundaryNe : state.memory.alpha.expectedBoundary ≠
      currentBidirectionalInput? transitionFuel state)
    (expectedWork : state.memory.expectedWork = some workInput)
    (workLength : workInput.length = 41) :
    (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
      answer).alpha.alpha =
      alphaZeroAfterMemory transitionFuel boundaryIndex
        (foldArmedAlphaIndexedState (bidirectionalAlphaState state)) answer := by
  have foldProjection :=
    fold_armed_alpha_projects_to_alpha_zero_after_boundary transitionFuel
      boundaryIndex (bidirectionalAlphaState state) answer afterBoundary (by
        simpa [bidirectionalAlphaState, currentBidirectionalInput?] using
          expectedBoundaryNe)
  unfold bidirectionalFoldAlphaAfterMemory
  simp only [afterAnchor, ↓reduceDIte]
  let current := currentBidirectionalInput? transitionFuel state
  let alphaState := foldArmedAlphaIndexedState (bidirectionalAlphaState state)
  let rawNext := foldArmedAlphaAfterMemory transitionFuel
    (bidirectionalAlphaState state) answer
  by_cases consumes : state.memory.foldUsed = false ∧
      matchesExpectedFoldWork current state.memory.expectedWork
  · have currentWork : current = some workInput := by
      rcases consumes.2 with ⟨input, currentExact, expectedExact⟩
      rw [expectedWork] at expectedExact
      have workEq : workInput = input := Option.some.inj expectedExact
      simpa [current, workEq] using currentExact
    have alphaNone : alphaZeroPreferredSlot transitionFuel alphaState = none := by
      apply alpha_zero_preferred_none_of_input_length_ne transitionFuel
        alphaState workInput
      · simpa [alphaState, current, currentBidirectionalInput?,
          bidirectionalAlphaState, foldArmedAlphaIndexedState] using currentWork
      · omega
    have rawUsed : rawNext.alpha.usedSlots =
        state.memory.alpha.alpha.usedSlots := by
      dsimp [rawNext]
      rw [fold_armed_alpha_after_memory_used_slots]
      change (match alphaZeroPreferredSlot transitionFuel alphaState with
        | none => state.memory.alpha.alpha.usedSlots
        | some slot => insert slot state.memory.alpha.alpha.usedSlots) = _
      rw [alphaNone]
    have overwrittenAlpha :
        { rawNext.alpha with
            usedSlots := state.memory.alpha.alpha.usedSlots } = rawNext.alpha := by
      cases alphaExact : rawNext.alpha with
      | mk producers usedSlots =>
          rw [alphaExact] at rawUsed
          simp only at rawUsed
          change
            ({ producers := producers
               usedSlots := state.memory.alpha.alpha.usedSlots } :
              AlphaZeroControllerMemory) =
            { producers := producers, usedSlots := usedSlots }
          cases rawUsed
          rfl
    rw [if_pos consumes]
    change { rawNext.alpha with
        usedSlots := state.memory.alpha.alpha.usedSlots } = _
    rw [overwrittenAlpha]
    simpa [rawNext] using foldProjection
  · rw [if_neg consumes]
    simpa [rawNext] using foldProjection

/-- General form of the post-boundary projection.  Work-first execution has
no pending work coordinate; boundary-first execution retains exactly one
41-byte coordinate. -/
theorem bidirectional_alpha_projects_to_alpha_zero_after_boundary_optional
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) (expectedWork : Option ShaInput)
    (afterAnchor : state.exposureIndex ≠ anchorIndex)
    (afterBoundary : state.exposureIndex ≠ boundaryIndex)
    (expectedBoundaryNe : state.memory.alpha.expectedBoundary ≠
      currentBidirectionalInput? transitionFuel state)
    (expectedWorkExact : state.memory.expectedWork = expectedWork)
    (workSafe : ∀ workInput, expectedWork = some workInput →
      workInput.length = 41) :
    (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
      answer).alpha.alpha =
      alphaZeroAfterMemory transitionFuel boundaryIndex
        (foldArmedAlphaIndexedState (bidirectionalAlphaState state)) answer := by
  cases expectedWork with
  | some workInput =>
      exact bidirectional_alpha_projects_to_alpha_zero_after_boundary
        transitionFuel anchorIndex boundaryIndex state answer workInput
          afterAnchor afterBoundary expectedBoundaryNe expectedWorkExact
          (workSafe workInput rfl)
  | none =>
      have foldProjection :=
        fold_armed_alpha_projects_to_alpha_zero_after_boundary transitionFuel
          boundaryIndex (bidirectionalAlphaState state) answer afterBoundary (by
            simpa [bidirectionalAlphaState, currentBidirectionalInput?] using
              expectedBoundaryNe)
      unfold bidirectionalFoldAlphaAfterMemory
      simp only [afterAnchor, ↓reduceDIte]
      have noConsumes : ¬ (state.memory.foldUsed = false ∧
          matchesExpectedFoldWork
            (currentBidirectionalInput? transitionFuel state)
            state.memory.expectedWork) := by
        intro consumes
        rw [expectedWorkExact] at consumes
        exact no_expected_fold_work_does_not_match _ consumes.2
      rw [if_neg noConsumes]
      exact foldProjection

/-- An ordinary dynamic alpha step never changes the selected boundary. -/
theorem fold_armed_alpha_after_memory_expected_boundary
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      FoldArmedAlphaZeroMemory)
    (answer : Digest256) :
    (foldArmedAlphaAfterMemory transitionFuel state answer).expectedBoundary =
      state.memory.expectedBoundary := by
  unfold foldArmedAlphaAfterMemory
  split <;> rfl

/-- Past the unique pair anchor, the wrapper retains both selected-pair
coordinates; only their one-shot consumption flags can change. -/
theorem bidirectional_after_nonanchor_preserves_pair_coordinates
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256)
    (notAnchor : state.exposureIndex ≠ anchorIndex) :
    let next := bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex
      state answer
    next.expectedWork = state.memory.expectedWork ∧
      next.alpha.expectedBoundary = state.memory.alpha.expectedBoundary := by
  unfold bidirectionalFoldAlphaAfterMemory
  simp only [notAnchor, ↓reduceDIte]
  let rawNext := foldArmedAlphaAfterMemory transitionFuel
    (bidirectionalAlphaState state) answer
  by_cases consumes : state.memory.foldUsed = false ∧
      matchesExpectedFoldWork
        (currentBidirectionalInput? transitionFuel state)
        state.memory.expectedWork
  · rw [if_pos consumes]
    constructor
    · trivial
    change rawNext.expectedBoundary = state.memory.alpha.expectedBoundary
    simpa [rawNext, bidirectionalAlphaState] using
      fold_armed_alpha_after_memory_expected_boundary transitionFuel
        (bidirectionalAlphaState state) answer
  · rw [if_neg consumes]
    constructor
    · trivial
    change rawNext.expectedBoundary = state.memory.alpha.expectedBoundary
    simpa [rawNext, bidirectionalAlphaState] using
      fold_armed_alpha_after_memory_expected_boundary transitionFuel
        (bidirectionalAlphaState state) answer

/-! ## Replay relation after the selected boundary -/

/-- Before its selected ordinal, the standalone controller cannot create a
producer or consume a slot from an inactive state. -/
theorem alpha_zero_inactive_step_before_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (notBoundary : state.exposureIndex ≠ boundaryIndex)
    (inactive : state.memory = inactiveAlphaZeroMemory) :
    (alphaZeroAfterMemory transitionFuel boundaryIndex state answer) =
      inactiveAlphaZeroMemory := by
  unfold alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => exact inactive
  | some input =>
      simp [inputExact, notBoundary, inactive, inactiveAlphaZeroMemory,
        alphaZeroPreferredSlot, alphaZeroOutputSlot?, updateAlphaZeroProducers,
        alphaZeroAdvancedSlot?]

/-- An inactive standalone alpha state stays exactly inactive throughout any
prefix ending no later than its selected boundary ordinal. -/
theorem alpha_zero_inactive_replay_before_boundary
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      state.memory = inactiveAlphaZeroMemory →
      state.exposureIndex + records.length ≤ boundaryIndex →
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex)
        records state).memory = inactiveAlphaZeroMemory := by
  intro records
  induction records with
  | nil =>
      intro state inactive _bounded
      simpa only [indexed_state_after_records_nil] using inactive
  | cons record records ih =>
      intro state inactive bounded
      let controller := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have notBoundary : state.exposureIndex ≠ boundaryIndex := by
        simp only [List.length_cons] at bounded
        omega
      have nextInactive : next.memory = inactiveAlphaZeroMemory := by
        change alphaZeroAfterMemory transitionFuel boundaryIndex state
          record.answer = inactiveAlphaZeroMemory
        exact alpha_zero_inactive_step_before_boundary transitionFuel
          boundaryIndex state record.answer notBoundary inactive
      have nextBounded : next.exposureIndex + records.length ≤ boundaryIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at bounded ⊢
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextInactive nextBounded

/-- After the selected boundary, the bidirectional controller and the
standalone alpha controller share the exact cursor, exposure ordinal, and
alpha memory.  The remaining fields retain the two literal selected-pair
coordinates needed to treat a later work exposure as alpha-inert. -/
def BidirectionalAlphaProjection
    {globalOracleCalls : Nat}
    (anchorIndex boundaryIndex : Nat) (boundaryInput : ShaInput)
    (expectedWork : Option ShaInput)
    (bidirectional : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (standalone : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory) : Prop :=
  bidirectional.exposureIndex = standalone.exposureIndex ∧
    bidirectional.cursor = standalone.cursor ∧
    bidirectional.memory.alpha.alpha = standalone.memory ∧
    bidirectional.memory.alpha.expectedBoundary = some boundaryInput ∧
    bidirectional.memory.expectedWork = expectedWork ∧
    anchorIndex < bidirectional.exposureIndex

/-- One post-boundary exposure preserves the exact projection.  The current
input need only differ from the already-consumed boundary input; it may be the
selected work input, whose 41-byte length makes that exceptional branch
alpha-inert. -/
theorem bidirectional_alpha_projection_step
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (boundaryInput input : ShaInput) (expectedWork : Option ShaInput)
    (bidirectional : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (standalone : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (projection : BidirectionalAlphaProjection anchorIndex boundaryIndex
      boundaryInput expectedWork bidirectional standalone)
    (inputExact : currentBidirectionalInput? transitionFuel bidirectional =
      some input)
    (inputNe : input ≠ boundaryInput)
    (notBoundaryIndex : bidirectional.exposureIndex ≠ boundaryIndex)
    (workSafe : ∀ workInput, expectedWork = some workInput →
      workInput.length = 41) :
    BidirectionalAlphaProjection anchorIndex boundaryIndex boundaryInput
      expectedWork
      ((bidirectionalFoldAlphaController transitionFuel anchorIndex).afterAnswer
        transitionFuel bidirectional answer)
      ((alphaZeroCausalController transitionFuel boundaryIndex).afterAnswer
        transitionFuel standalone answer) := by
  rcases projection with
    ⟨exposureExact, cursorExact, alphaExact, boundaryExact, workExact,
      afterAnchor⟩
  have boundaryNe : bidirectional.memory.alpha.expectedBoundary ≠
      currentBidirectionalInput? transitionFuel bidirectional := by
    rw [boundaryExact, inputExact]
    exact fun equal => inputNe (Option.some.inj equal).symm
  have projected :=
    bidirectional_alpha_projects_to_alpha_zero_after_boundary_optional
    transitionFuel anchorIndex boundaryIndex bidirectional answer expectedWork
      (Nat.ne_of_lt afterAnchor).symm notBoundaryIndex
      boundaryNe workExact workSafe
  have pairPreserved := bidirectional_after_nonanchor_preserves_pair_coordinates
    transitionFuel anchorIndex bidirectional answer
      (Nat.ne_of_lt afterAnchor).symm
  unfold BidirectionalAlphaProjection
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [exposureExact]
  · simp [cursorExact]
  · change
      (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex
        bidirectional answer).alpha.alpha =
      alphaZeroAfterMemory transitionFuel boundaryIndex standalone answer
    simpa [foldArmedAlphaIndexedState, bidirectionalAlphaState, alphaExact,
      exposureExact, cursorExact] using projected
  · change
      (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex
        bidirectional answer).alpha.expectedBoundary = some boundaryInput
    exact pairPreserved.2.trans boundaryExact
  · change
      (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex
        bidirectional answer).expectedWork = expectedWork
    exact pairPreserved.1.trans workExact
  · simp only [indexed_after_answer_exposure_index]
    omega

/-- The pointwise projection lifts through any aligned machine-only suffix
that does not repeat the already-consumed boundary coordinate. -/
theorem bidirectional_alpha_projection_replay
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (boundaryInput : ShaInput) (expectedWork : Option ShaInput) :
    ∀ (records : List UnifiedExposureRecord)
      (bidirectional : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory)
      (standalone : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      BidirectionalAlphaProjection anchorIndex boundaryIndex boundaryInput
        expectedWork bidirectional standalone →
      boundaryIndex < bidirectional.exposureIndex →
      IndexedRecordsAligned transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        bidirectional records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records, causalInput? record ≠ some boundaryInput) →
      (∀ workInput, expectedWork = some workInput →
        workInput.length = 41) →
      BidirectionalAlphaProjection anchorIndex boundaryIndex boundaryInput
        expectedWork
        (indexedStateAfterRecords transitionFuel
          (bidirectionalFoldAlphaController transitionFuel anchorIndex)
          records bidirectional)
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records standalone) := by
  intro records
  induction records with
  | nil =>
      intro bidirectional standalone projection _afterBoundary _aligned _only
        _avoids _safe
      simpa only [indexed_state_after_records_nil] using projection
  | cons record records ih =>
      intro bidirectional standalone projection afterBoundary aligned
        onlyMachine avoids workSafe
      obtain ⟨actor, input, answer, recordExact⟩ :=
        onlyMachine record List.mem_cons_self
      subst record
      have headAligned := aligned []
        (.machineFresh actor input answer) records rfl
      have inputExact :
          currentBidirectionalInput? transitionFuel bidirectional =
            some input := by
        simpa [currentBidirectionalInput?] using
          aligned_machine_record_has_exact_input transitionFuel
            bidirectional.cursor actor input answer headAligned
      have inputNe : input ≠ boundaryInput := by
        intro equal
        apply avoids (.machineFresh actor input answer) List.mem_cons_self
        simp [causalInput?, equal]
      let bidirectionalController := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let standaloneController := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let nextBidirectional := bidirectionalController.afterAnswer
        transitionFuel bidirectional answer
      let nextStandalone := standaloneController.afterAnswer
        transitionFuel standalone answer
      have nextProjection : BidirectionalAlphaProjection anchorIndex
          boundaryIndex boundaryInput expectedWork nextBidirectional
          nextStandalone := by
        simpa [bidirectionalController, standaloneController,
          nextBidirectional, nextStandalone] using
          bidirectional_alpha_projection_step transitionFuel anchorIndex
            boundaryIndex boundaryInput input expectedWork bidirectional
              standalone answer projection inputExact inputNe
                (Nat.ne_of_lt afterBoundary).symm workSafe
      have tailAligned : IndexedRecordsAligned transitionFuel
          bidirectionalController nextBidirectional records := by
        apply indexed_records_aligned_segment transitionFuel
          bidirectionalController bidirectional
          ((.machineFresh actor input answer) :: records)
          [(.machineFresh actor input answer)] records []
        · simpa [bidirectionalController] using aligned
        · simp [nextBidirectional, UnifiedExposureRecord.answer]
      have tailOnly : OnlyMachineFreshRecords records := by
        intro tailRecord member
        exact onlyMachine tailRecord (List.mem_cons_of_mem _ member)
      have tailAvoids : ∀ tailRecord ∈ records,
          causalInput? tailRecord ≠ some boundaryInput := by
        intro tailRecord member
        exact avoids tailRecord (List.mem_cons_of_mem _ member)
      rw [indexed_state_after_records_cons,
        indexed_state_after_records_cons]
      apply ih nextBidirectional nextStandalone nextProjection
      · simp only [nextBidirectional, indexed_after_answer_exposure_index]
        omega
      · exact tailAligned
      · exact tailOnly
      · exact tailAvoids
      · exact workSafe

/-- The same projection may begin at a work-first anchor and run up to, but
not including, the later boundary record.  The ordinal bound supplies the
standalone controller's non-boundary condition at every consumed step. -/
theorem bidirectional_alpha_projection_replay_before_boundary
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex boundaryIndex : Nat)
    (boundaryInput : ShaInput) (expectedWork : Option ShaInput) :
    ∀ (records : List UnifiedExposureRecord)
      (bidirectional : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory)
      (standalone : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      BidirectionalAlphaProjection anchorIndex boundaryIndex boundaryInput
        expectedWork bidirectional standalone →
      bidirectional.exposureIndex + records.length ≤ boundaryIndex →
      IndexedRecordsAligned transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        bidirectional records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records, causalInput? record ≠ some boundaryInput) →
      (∀ workInput, expectedWork = some workInput →
        workInput.length = 41) →
      BidirectionalAlphaProjection anchorIndex boundaryIndex boundaryInput
        expectedWork
        (indexedStateAfterRecords transitionFuel
          (bidirectionalFoldAlphaController transitionFuel anchorIndex)
          records bidirectional)
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records standalone) := by
  intro records
  induction records with
  | nil =>
      intro bidirectional standalone projection _bounded _aligned _only
        _avoids _safe
      simpa only [indexed_state_after_records_nil] using projection
  | cons record records ih =>
      intro bidirectional standalone projection bounded aligned onlyMachine
        avoids workSafe
      obtain ⟨actor, input, answer, recordExact⟩ :=
        onlyMachine record List.mem_cons_self
      subst record
      have headAligned := aligned []
        (.machineFresh actor input answer) records rfl
      have inputExact :
          currentBidirectionalInput? transitionFuel bidirectional =
            some input := by
        simpa [currentBidirectionalInput?] using
          aligned_machine_record_has_exact_input transitionFuel
            bidirectional.cursor actor input answer headAligned
      have inputNe : input ≠ boundaryInput := by
        intro equal
        apply avoids (.machineFresh actor input answer) List.mem_cons_self
        simp [causalInput?, equal]
      have notBoundaryIndex : bidirectional.exposureIndex ≠ boundaryIndex := by
        simp only [List.length_cons] at bounded
        omega
      let bidirectionalController := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let standaloneController := alphaZeroCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel boundaryIndex
      let nextBidirectional := bidirectionalController.afterAnswer
        transitionFuel bidirectional answer
      let nextStandalone := standaloneController.afterAnswer
        transitionFuel standalone answer
      have nextProjection : BidirectionalAlphaProjection anchorIndex
          boundaryIndex boundaryInput expectedWork nextBidirectional
          nextStandalone := by
        simpa [bidirectionalController, standaloneController,
          nextBidirectional, nextStandalone] using
          bidirectional_alpha_projection_step transitionFuel anchorIndex
            boundaryIndex boundaryInput input expectedWork bidirectional
              standalone answer projection inputExact inputNe notBoundaryIndex
                workSafe
      have nextBounded : nextBidirectional.exposureIndex + records.length ≤
          boundaryIndex := by
        simp only [nextBidirectional, indexed_after_answer_exposure_index,
          List.length_cons] at bounded ⊢
        omega
      have tailAligned : IndexedRecordsAligned transitionFuel
          bidirectionalController nextBidirectional records := by
        apply indexed_records_aligned_segment transitionFuel
          bidirectionalController bidirectional
          ((.machineFresh actor input answer) :: records)
          [(.machineFresh actor input answer)] records []
        · simpa [bidirectionalController] using aligned
        · simp
      have tailOnly : OnlyMachineFreshRecords records := by
        intro tailRecord member
        exact onlyMachine tailRecord (List.mem_cons_of_mem _ member)
      have tailAvoids : ∀ tailRecord ∈ records,
          causalInput? tailRecord ≠ some boundaryInput := by
        intro tailRecord member
        exact avoids tailRecord (List.mem_cons_of_mem _ member)
      rw [indexed_state_after_records_cons,
        indexed_state_after_records_cons]
      exact ih nextBidirectional nextStandalone nextProjection nextBounded
        tailAligned tailOnly tailAvoids workSafe
end

#print axioms alpha_zero_preferred_none_of_input_length_ne
#print axioms literal_fold_work_length
#print axioms fold_armed_alpha_projects_to_alpha_zero_after_boundary
#print axioms bidirectional_alpha_projects_to_alpha_zero_after_boundary
#print axioms bidirectional_alpha_projects_to_alpha_zero_after_boundary_optional
#print axioms fold_armed_alpha_after_memory_expected_boundary
#print axioms bidirectional_after_nonanchor_preserves_pair_coordinates
#print axioms alpha_zero_inactive_step_before_boundary
#print axioms alpha_zero_inactive_replay_before_boundary
#print axioms BidirectionalAlphaProjection
#print axioms bidirectional_alpha_projection_step
#print axioms bidirectional_alpha_projection_replay
#print axioms bidirectional_alpha_projection_replay_before_boundary

end AspisK1.V7Tag73BidirectionalFoldAlphaProjection

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
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedExposureCausalRouter
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

end

#print axioms alpha_zero_preferred_none_of_input_length_ne
#print axioms literal_fold_work_length
#print axioms fold_armed_alpha_projects_to_alpha_zero_after_boundary
#print axioms bidirectional_alpha_projects_to_alpha_zero_after_boundary

end AspisK1.V7Tag73BidirectionalFoldAlphaProjection

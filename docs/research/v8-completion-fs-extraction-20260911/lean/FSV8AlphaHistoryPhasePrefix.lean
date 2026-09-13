import FSV8AlphaCompleteCoordinateRouter

/-!
# Source-shaped ordinary-alpha history prefixes

This leaf records the deterministic half of the missing V8 alpha source
coupling.  Starting from the literal round-zero marker, every rejected duplex
block advances the history recognizer from output slot `i` through advance
slot `i` to output slot `i+1`.  The current digest and both answers remain
arbitrary, so the statement applies to adaptive candidate execution and to
cached as well as fresh calls.

It does not claim that a call was fresh, that a routed coordinate supplied its
answer, or that a successful decoder path occurred in the exact root.  Those
are the next source/origin and realization bridges.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlphaHistoryPhasePrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

abbrev Block := Digest256

def outputRecord (digest answer : Block) (origin : AnswerOrigin) : QueryRecord :=
  { input := bytes digest ++ [domSqueeze]
    output := answer
    actor := .verifier
    origin := origin }

def advanceRecord (digest answer : Block) (origin : AnswerOrigin) : QueryRecord :=
  { input := bytes digest ++ [domAdvance]
    output := answer
    actor := .verifier
    origin := origin }

def markerRecord (digest answer : Block) (nonce : NonceBytes)
    (origin : AnswerOrigin) : QueryRecord :=
  { input := bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce
    output := answer
    actor := .verifier
    origin := origin }

@[simp] theorem alpha_marker_of_output_input (digest : Block) :
    relationAlphaMarkerOfInput? (bytes digest ++ [domSqueeze]) = none := by
  simp [relationAlphaMarkerOfInput?, laterRelationRoundOfInput?,
    semanticAbsorbLabelOfInput?, bytes_length]

@[simp] theorem alpha_marker_of_advance_input (digest : Block) :
    relationAlphaMarkerOfInput? (bytes digest ++ [domAdvance]) = none := by
  simp [relationAlphaMarkerOfInput?, laterRelationRoundOfInput?,
    semanticAbsorbLabelOfInput?, bytes_length]

@[simp] theorem phase_after_marker
    (history : List QueryRecord) (digest answer : Block) (nonce : NonceBytes)
    (origin : AnswerOrigin) :
    relationAlphaHistoryPhase 0
        (history ++ [markerRecord digest answer nonce origin]) = .output [] := by
  rw [relation_alpha_history_phase_append_verifier]
  · exact alpha_zero_phase_after_literal_fold_nonce
      (relationAlphaHistoryPhase 0 history) digest answer nonce origin
  · rfl

@[simp] theorem phase_after_output
    (history : List QueryRecord) (prior : List Block) (digest answer : Block)
    (origin : AnswerOrigin)
    (phase : relationAlphaHistoryPhase 0 history = .output prior) :
    relationAlphaHistoryPhase 0
        (history ++ [outputRecord digest answer origin]) =
      .advance prior answer := by
  rw [relation_alpha_history_phase_append_verifier]
  · simp [RelationAlphaHistoryPhase.afterVerifierRecord, outputRecord, phase]
  · rfl

@[simp] theorem phase_after_rejected_advance
    (history : List QueryRecord) (prior : List Block)
    (current digest answer : Block) (origin : AnswerOrigin)
    (phase : relationAlphaHistoryPhase 0 history = .advance prior current)
    (rejected : decodeChallengeParameter exactSecureCircleParameterMap
      (.alpha 0) (prior ++ [current]) = none) :
    relationAlphaHistoryPhase 0
        (history ++ [advanceRecord digest answer origin]) =
      .output (prior ++ [current]) := by
  rw [relation_alpha_history_phase_append_verifier]
  · simp [RelationAlphaHistoryPhase.afterVerifierRecord, advanceRecord, phase,
      rejected]
  · rfl

@[simp] theorem phase_after_accepted_advance
    (history : List QueryRecord) (prior : List Block)
    (current digest answer : Block) (origin : AnswerOrigin) (value : Qm31Bytes)
    (phase : relationAlphaHistoryPhase 0 history = .advance prior current)
    (accepted : decodeChallengeParameter exactSecureCircleParameterMap
      (.alpha 0) (prior ++ [current]) = some value) :
    relationAlphaHistoryPhase 0
        (history ++ [advanceRecord digest answer origin]) = .inactive := by
  rw [relation_alpha_history_phase_append_verifier]
  · simp [RelationAlphaHistoryPhase.afterVerifierRecord, advanceRecord, phase,
      accepted]
  · rfl

theorem preferred_output_slot
    (history : List QueryRecord) (prior : List Block) (digest : Block)
    (phase : relationAlphaHistoryPhase 0 history = .output prior)
    (bounded : prior.length < 4) :
    relationAlphaPreferredSlotFromHistory 0 history
        (bytes digest ++ [domSqueeze]) =
      some (⟨prior.length, bounded⟩, 0) := by
  simp [relationAlphaPreferredSlotFromHistory, phase, bounded]

theorem preferred_advance_slot
    (history : List QueryRecord) (prior : List Block)
    (current digest : Block)
    (phase : relationAlphaHistoryPhase 0 history = .advance prior current)
    (bounded : prior.length < 4) :
    relationAlphaPreferredSlotFromHistory 0 history
        (bytes digest ++ [domAdvance]) =
      some (⟨prior.length, bounded⟩, 1) := by
  simp [relationAlphaPreferredSlotFromHistory, phase, bounded]

/-- A prefix ending immediately before the next output query.  Every stored
block is one that the literal decoder rejected, so no accepted attempt is
silently continued. -/
inductive RejectedCandidatePrefix : List QueryRecord → List Block → Prop where
  | marker (history : List QueryRecord) (digest answer : Block)
      (nonce : NonceBytes) (origin : AnswerOrigin) :
      RejectedCandidatePrefix
        (history ++ [markerRecord digest answer nonce origin]) []
  | rejected {history : List QueryRecord} {prior : List Block}
      (priorPath : RejectedCandidatePrefix history prior)
      (bounded : prior.length < 4)
      (digest output advanced : Block)
      (outputOrigin advanceOrigin : AnswerOrigin)
      (reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [output]) = none) :
      RejectedCandidatePrefix
        (history ++ [outputRecord digest output outputOrigin,
          advanceRecord digest advanced advanceOrigin])
        (prior ++ [output])

theorem rejectedCandidatePrefix_phase :
    ∀ {history : List QueryRecord} {prior : List Block},
      RejectedCandidatePrefix history prior →
        relationAlphaHistoryPhase 0 history = .output prior := by
  intro history prior path
  induction path with
  | marker history digest answer nonce origin =>
      exact phase_after_marker history digest answer nonce origin
  | @rejected history prior priorPath bounded digest output advanced
      outputOrigin advanceOrigin reject ih =>
      rw [show history ++ [outputRecord digest output outputOrigin,
          advanceRecord digest advanced advanceOrigin] =
        (history ++ [outputRecord digest output outputOrigin]) ++
          [advanceRecord digest advanced advanceOrigin] by simp]
      apply phase_after_rejected_advance _ prior output digest advanced
        advanceOrigin
      · exact phase_after_output history prior digest output outputOrigin ih
      · exact reject

/-- Both literal inputs of the next adaptive duplex pair are labelled by the
same next block index. -/
theorem rejectedCandidatePrefix_next_slots
    {history : List QueryRecord} {prior : List Block}
    (path : RejectedCandidatePrefix history prior)
    (bounded : prior.length < 4) (digest output : Block)
    (origin : AnswerOrigin) :
    relationAlphaPreferredSlotFromHistory 0 history
        (bytes digest ++ [domSqueeze]) =
        some (⟨prior.length, bounded⟩, 0) ∧
      relationAlphaPreferredSlotFromHistory 0
          (history ++ [outputRecord digest output origin])
          (bytes digest ++ [domAdvance]) =
        some (⟨prior.length, bounded⟩, 1) := by
  have phase := rejectedCandidatePrefix_phase path
  exact ⟨preferred_output_slot history prior digest phase bounded,
    preferred_advance_slot
      (history ++ [outputRecord digest output origin]) prior output digest
      (phase_after_output history prior digest output origin phase) bounded⟩

#print axioms phase_after_marker
#print axioms phase_after_output
#print axioms phase_after_rejected_advance
#print axioms phase_after_accepted_advance
#print axioms preferred_output_slot
#print axioms preferred_advance_slot
#print axioms rejectedCandidatePrefix_phase
#print axioms rejectedCandidatePrefix_next_slots

end
end AspisV8Completion.FSV8AlphaHistoryPhasePrefix

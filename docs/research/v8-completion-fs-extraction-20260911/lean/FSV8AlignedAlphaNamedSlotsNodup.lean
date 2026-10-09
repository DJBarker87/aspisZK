import FSV8AlignedAlphaChallengeRun

/-!
# Duplicate-free named slots for one accepted V8 alpha candidate

This leaf proves the source-local uniqueness fact needed by the causal alpha
router. Every rejected output/advance pair consumes the next block index, and
the accepted pair consumes the following index. Cached calls remain in the
source history but expose no root-tape coordinate, so their slots are omitted.

The unrestricted slot-machine statement is false: a second literal
round-zero marker resets the phase and can reuse slot zero. The endpoint below
is therefore restricted to the actual one-marker `AlignedRejectedPath`
grammar. A later bridge must identify the exact-root named records with the
fresh slots constructed here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlignedAlphaNamedSlotsNodup

open FSBoundedTranscript
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaChallengeRun
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

def freshSlot (origin : AnswerOrigin) (slot : RelationAlphaDuplexSlot) :
    List RelationAlphaDuplexSlot :=
  match origin with
  | .fresh => [slot]
  | .cached | .programmed => []

theorem mem_freshSlot_eq {origin : AnswerOrigin}
    {slot candidate : RelationAlphaDuplexSlot}
    (member : candidate ∈ freshSlot origin slot) : candidate = slot := by
  cases origin <;> simp [freshSlot] at member ⊢
  exact member

theorem append_fresh_pair_nodup
    {count : Nat} {slots : List RelationAlphaDuplexSlot}
    (bounded : count < 4) (priorNodup : slots.Nodup)
    (priorLt : ∀ slot ∈ slots, slot.1.val < count)
    (outputOrigin advanceOrigin : AnswerOrigin) :
    (slots ++ freshSlot outputOrigin (⟨count, bounded⟩, 0) ++
      freshSlot advanceOrigin (⟨count, bounded⟩, 1)).Nodup := by
  let outputSlot : RelationAlphaDuplexSlot := (⟨count, bounded⟩, 0)
  let advanceSlot : RelationAlphaDuplexSlot := (⟨count, bounded⟩, 1)
  let newSlots := freshSlot outputOrigin outputSlot ++
    freshSlot advanceOrigin advanceSlot
  have outputNeAdvance : outputSlot ≠ advanceSlot := by
    intro equal
    have halves := congrArg Prod.snd equal
    simpa [outputSlot, advanceSlot] using halves
  have newNodup : newSlots.Nodup := by
    cases outputOrigin <;> cases advanceOrigin <;>
      simp [newSlots, freshSlot, outputNeAdvance]
  have newFirst : ∀ slot ∈ newSlots,
      slot.1 = (⟨count, bounded⟩ : Fin 4) := by
    intro slot member
    rcases List.mem_append.mp member with outputMember | advanceMember
    · have exactSlot := mem_freshSlot_eq outputMember
      subst slot
      rfl
    · have exactSlot := mem_freshSlot_eq advanceMember
      subst slot
      rfl
  have separated : ∀ old ∈ slots, ∀ fresh ∈ newSlots, old ≠ fresh := by
    intro old oldMember fresh newMember equalSlots
    have strict := priorLt old oldMember
    have freshFirst := newFirst fresh newMember
    have equalFirst := congrArg Prod.fst equalSlots
    have equal : old.1 = (⟨count, bounded⟩ : Fin 4) :=
      equalFirst.trans freshFirst
    have values := congrArg Fin.val equal
    simp only at values
    omega
  rw [List.append_assoc]
  change (slots ++ newSlots).Nodup
  exact List.nodup_append.mpr ⟨priorNodup, newNodup, separated⟩

/-- Source grammar for the fresh slots of zero or more rejected alpha pairs.
The index is generated from the number of earlier pairs. -/
inductive CandidateFreshSlots : Nat → List RelationAlphaDuplexSlot → Prop where
  | nil : CandidateFreshSlots 0 []
  | pair {count : Nat} {slots : List RelationAlphaDuplexSlot}
      (prior : CandidateFreshSlots count slots)
      (bounded : count < 4) (outputOrigin advanceOrigin : AnswerOrigin) :
      CandidateFreshSlots (count + 1)
        (slots ++ freshSlot outputOrigin (⟨count, bounded⟩, 0) ++
          freshSlot advanceOrigin (⟨count, bounded⟩, 1))

/-- The same grammar indexed by the literal aligned source proof. Unlike the
count-only relation, this records the actual fresh/cache origins of every
pair, and so gives a non-vacuous bridge target for exact-root labels. -/
inductive AlignedPathFreshSlots
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} → {v7 : OracleState} → {s : Transcript} →
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s →
        List RelationAlphaDuplexSlot → Prop where
  | base (aligned : FSV8V7StateAlignment.StateAligned tape finiteTape startV7
        start.oracle)
      (prefixPath : FSV8AlphaHistoryPhasePrefix.RejectedCandidatePrefix
        startV7.history []) :
      AlignedPathFreshSlots (.base aligned prefixPath) []
  | snoc {prior : List Block} {v7 : OracleState} {s : Transcript}
      {path : AlignedRejectedPath tape finiteTape limits startV7 start
        prior v7 s}
      {pair : AlignedSqueezePair tape finiteTape limits v7 s}
      {bounded : prior.length < 4}
      {reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(FSV8CandidateOriginTrace.outputStep tape s).1]) =
          none}
      {slots : List RelationAlphaDuplexSlot}
      (source : AlignedPathFreshSlots path slots) :
      AlignedPathFreshSlots (.snoc path pair bounded reject)
        (slots ++ freshSlot pair.outputOrigin (⟨prior.length, bounded⟩, 0) ++
          freshSlot pair.advanceOrigin (⟨prior.length, bounded⟩, 1))

theorem AlignedPathFreshSlots.candidate_source
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {v7 : OracleState} {s : Transcript}
    {path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s}
    {slots : List RelationAlphaDuplexSlot}
    (source : AlignedPathFreshSlots path slots) :
    CandidateFreshSlots blocks.length slots := by
  induction source with
  | base => exact .nil
  | @snoc prior v7 s path pair bounded reject slots source ih =>
      simpa using CandidateFreshSlots.pair ih bounded pair.outputOrigin
        pair.advanceOrigin

/-- The source path constructs its slot grammar without inspecting future
answers. Origins come from the actual aligned pair records. -/
theorem AlignedRejectedPath.constructs_candidate_fresh_slots
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    ∀ {blocks : List Block} {v7 : OracleState} {s : Transcript}
      (path : AlignedRejectedPath tape finiteTape limits startV7 start
        blocks v7 s),
      ∃ slots, AlignedPathFreshSlots path slots := by
  intro blocks v7 s path
  induction path with
  | base aligned prefixPath => exact ⟨[], .base aligned prefixPath⟩
  | @snoc prior v7 s path pair bounded reject ih =>
      rcases ih with ⟨slots, slotsSource⟩
      refine ⟨slots ++ freshSlot pair.outputOrigin
          (⟨prior.length, bounded⟩, 0) ++
          freshSlot pair.advanceOrigin (⟨prior.length, bounded⟩, 1), ?_⟩
      exact .snoc (reject := reject) slotsSource

/-- Every earlier generated slot has smaller first coordinate than the next
pair index, and the generated list has no duplicates. -/
theorem candidate_fresh_slots_nodup_and_lt :
    ∀ {count : Nat} {slots : List RelationAlphaDuplexSlot},
      CandidateFreshSlots count slots →
        slots.Nodup ∧ ∀ slot ∈ slots, slot.1.val < count := by
  intro count slots source
  induction source with
  | nil => simp
  | @pair count slots source bounded outputOrigin advanceOrigin ih =>
      rcases ih with ⟨priorNodup, priorLt⟩
      refine ⟨append_fresh_pair_nodup bounded priorNodup priorLt
        outputOrigin advanceOrigin, ?_⟩
      · intro slot member
        rw [List.append_assoc] at member
        rcases List.mem_append.mp member with priorMember | newMember
        · exact Nat.lt_succ_of_lt (priorLt slot priorMember)
        · rcases List.mem_append.mp newMember with outputMember | advanceMember
          · have exactSlot := mem_freshSlot_eq outputMember
            subst slot
            simp
          · have exactSlot := mem_freshSlot_eq advanceMember
            subst slot
            simp

/-- The accepted final pair occupies the next still-unused block index.
Cached halves are absent, and no freshness premise is required. -/
theorem candidate_fresh_slots_append_final_nodup
    {count : Nat} {slots : List RelationAlphaDuplexSlot}
    (source : CandidateFreshSlots count slots) (bounded : count < 4)
    (outputOrigin advanceOrigin : AnswerOrigin) :
    (slots ++ freshSlot outputOrigin (⟨count, bounded⟩, 0) ++
      freshSlot advanceOrigin (⟨count, bounded⟩, 1)).Nodup := by
  obtain ⟨priorNodup, priorLt⟩ := candidate_fresh_slots_nodup_and_lt source
  exact append_fresh_pair_nodup bounded priorNodup priorLt outputOrigin
    advanceOrigin

/-- A successful source run of at most four blocks constructs one
duplicate-free fresh-slot list for all rejected pairs and its accepted final
pair. This supplies the source invariant, not yet its exact-root equality. -/
theorem successful_aligned_candidate_constructs_nodup_fresh_slots
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value)
    (blocksCap : blocks.length ≤ 4) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits beforeFinal
        finalStart,
      ∃ slots : List RelationAlphaDuplexSlot,
        AlignedPathFreshSlots path slots ∧
        ∃ bounded : rejected.length < 4,
          (slots ++ freshSlot finalPair.outputOrigin
              (⟨rejected.length, bounded⟩, 0) ++
            freshSlot finalPair.advanceOrigin
              (⟨rejected.length, bounded⟩, 1)).Nodup := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, blocksExact,
      finalExact, accepted, finalPhase⟩
  obtain ⟨slots, pathSlots⟩ :=
    AlignedRejectedPath.constructs_candidate_fresh_slots path
  have slotsSource := pathSlots.candidate_source
  have bounded : rejected.length < 4 := by
    rw [blocksExact] at blocksCap
    simp only [List.length_append, List.length_singleton] at blocksCap
    omega
  refine ⟨rejected, finalStart, beforeFinal, path, finalPair, slots, pathSlots,
    bounded, ?_⟩
  exact candidate_fresh_slots_append_final_nodup slotsSource bounded
    finalPair.outputOrigin finalPair.advanceOrigin

#print axioms AlignedRejectedPath.constructs_candidate_fresh_slots
#print axioms AlignedPathFreshSlots.candidate_source
#print axioms mem_freshSlot_eq
#print axioms append_fresh_pair_nodup
#print axioms candidate_fresh_slots_nodup_and_lt
#print axioms candidate_fresh_slots_append_final_nodup
#print axioms successful_aligned_candidate_constructs_nodup_fresh_slots

end
end AspisV8Completion.FSV8AlignedAlphaNamedSlotsNodup

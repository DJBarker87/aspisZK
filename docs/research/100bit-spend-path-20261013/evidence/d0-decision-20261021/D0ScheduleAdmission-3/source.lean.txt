import R16CanonRecorded
import R16DecisionQueryModel

/-! The erased schedule guard required before canonical retagging. This is
one check of the proposed decision, not the complete frozen verifier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.D0ScheduleAdmission
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
attribute [local instance] Classical.propDecidable

/-- Reject misplaced initial constructors and missing/extra completed rows.
The erased API cannot distinguish .payload from .second or .c2; canonical
retagging supplies exactly those typed distinctions. -/
def Schedule (p : ErasedPrefix) : Prop :=
  p.rounds.length = 33 ∧ ∀ i m c, p.rounds[i]? = some (m,c) →
    UnifiedSampler.messageValid i m

def guard (p : ErasedPrefix) (_ : ErasedMessage) : Bool := decide (Schedule p)

def withSchedule (core : ErasedPrefix → ErasedMessage → Bool)
    (p : ErasedPrefix) (m : ErasedMessage) : Bool := guard p m && core p m

theorem accepted_schedule (core : ErasedPrefix → ErasedMessage → Bool)
    (p : ErasedPrefix) (m : ErasedMessage)
    (h : withSchedule core p m = true) : Schedule p := by
  cases hg : guard p m with
  | false => simp [withSchedule, hg] at h
  | true => exact of_decide_eq_true hg

theorem reject_initial31 (core : ErasedPrefix → ErasedMessage → Bool)
    (p : ErasedPrefix) (m : ErasedMessage) (root : State)
    (c : LiteralTranscript.Challenge)
    (h : p.rounds[31]? = some (.initial root,c)) :
    withSchedule core p m = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have bad := (accepted_schedule core p m accepted).2 31 (.initial root) c h
  exact bad

/-- Admission gives the missing hypothesis of the total retagging lemma. -/
theorem shape_of_schedule (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (h : Schedule (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33))) :
    R16CanonReduction.Shape pf := by
  intro i hi
  exact h.2 i (LiteralTranscript.erase (pf i))
    (eval H (LiteralByteSampler.samp i
      ((LiteralByteProtocol.protocol D).transcript H pub pf i) (pf i)).toProgram).2 (by
    simp only [LiteralTranscript.erasePrefix, List.getElem?_map,
      LiteralByteRunFacts.transcript_index D H pub pf 33 i hi, Option.map_some])

theorem accepted_canonical_valid (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (accepted : (eval H (verifier D (withSchedule core) pub pf)).2 = true) :
    ∀ i, i < 33 → LiteralTranscript.valid i (R16CanonReduction.proof pf i) := by
  have ha : withSchedule core
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf 33))
      (LiteralTranscript.erase (pf 33)) = true := by
    rw [RawCutProverCompiler.verifier, FS2.verifier_eval] at accepted
    exact accepted
  exact R16CanonReduction.valid_of_shape pf
    (shape_of_schedule D H pub pf (accepted_schedule core _ _ ha))

/-- Enrichment changes only words, so the admitted canonical schedule survives. -/
theorem enrich_valid (w : CanonicalCutEnrichedTranscript.Words)
    (i : Nat) (m : LiteralTranscript.Message) (h : LiteralTranscript.valid i m) :
    LiteralTranscript.valid i (CanonicalCutEnrichedTranscript.enrichMessage w m) := by
  by_cases h0 : i = 0
  · subst i; cases m <;> simpa [CanonicalCutEnrichedTranscript.enrichMessage,
      LiteralTranscript.valid] using h
  · by_cases h2 : i = 2
    · subst i; cases m <;> simpa [CanonicalCutEnrichedTranscript.enrichMessage,
        LiteralTranscript.valid] using h
    · by_cases h30 : i = 30
      · subst i; cases m <;> simpa [CanonicalCutEnrichedTranscript.enrichMessage,
          LiteralTranscript.valid] using h
      · cases i with
        | zero => exact False.elim (h0 rfl)
        | succ i => cases m <;> simpa [CanonicalCutEnrichedTranscript.enrichMessage,
            LiteralTranscript.valid, h2, h30] using h

/-- Reduction works for every prover, without restricting its input domain. -/
theorem accepted_canon_prover_valid (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (accepted : FS2.accepts (eval H (original D (withSchedule core) P))) :
    ∀ i, i < 33 → LiteralTranscript.valid i
      ((eval H (R16CanonReduction.canon P)).2.2 i) := by
  rw [R16CanonReduction.eval_canon]
  apply accepted_canonical_valid D core H (eval H P).2.1 (eval H P).2.2
  change (eval H (original D (withSchedule core) P)).2.2 = true at accepted
  rw [RawCutProverCompiler.experiment_eval] at accepted
  exact accepted

/-- The reduction retains the exact failure probability and the query budget. -/
theorem arbitrary_prover_reduction (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (budget : DecoderQueryAccounting.AdversaryQueries P Q) :
    DecoderQueryAccounting.AdversaryQueries (R16CanonReduction.canon P) Q ∧
    AspisV8R19.MemoizedProgramLaw.lazyMean
      (recorded D (withSchedule core) (R16CanonReduction.canon P)) emptyTable
      RawRecordedOracleExtractionMassBin.failureMass =
    AspisV8R19.MemoizedProgramLaw.lazyMean
      (recorded D (withSchedule core) P) emptyTable
      RawRecordedOracleExtractionMassBin.failureMass :=
  ⟨R16CanonReduction.queries_canon P Q budget,
    R16CanonRecorded.recorded_failure D (withSchedule core) P⟩

#print axioms accepted_schedule
#print axioms reject_initial31
#print axioms shape_of_schedule
#print axioms accepted_canonical_valid
#print axioms enrich_valid
#print axioms accepted_canon_prover_valid
#print axioms arbitrary_prover_reduction
end AspisR1.D0ScheduleAdmission
end

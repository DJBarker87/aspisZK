import R16CanonRecorded
import R16DecisionQueryModel

/-! The requested universal canonical endpoint is obstructed by erased
initial/payload shape. This module states that obstruction on the actual
33-row transcript, and composes the independent typed checkpoint writer.
No premise-removing final_soundness is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessBinPerQueryCanon
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
open R16CanonReduction

-- Prevent definitional comparison from evaluating the concrete verifier.
-- Every acceptance proof below uses the symbolic verifier_eval theorem.
attribute [local irreducible] RawCutProverCompiler.verifier

theorem canon_erased_transcript (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof) (n : Nat) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub
      (R16CanonReduction.proof pf) n) =
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf n) :=
  R16DecisionErasure.erased_transcript_eq D H pub pf
    (R16CanonReduction.proof pf) (erase_proof pf) n

theorem erased_transcript_row (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (a b : LiteralProtocol.Proof) (i : Nat) (hi : i < 33)
    (same : LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub a 33) =
      LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub b 33)) :
    LiteralTranscript.erase (a i) = LiteralTranscript.erase (b i) := by
  have h := congrArg (fun p : ErasedPrefix => p.rounds[i]?) same
  simp only [LiteralTranscript.erasePrefix, List.getElem?_map,
    LiteralByteRunFacts.transcript_index D H pub a 33 i hi,
    LiteralByteRunFacts.transcript_index D H pub b 33 i hi, Option.map_some] at h
  exact congrArg Prod.fst (Option.some.inj h)

/-- Even an accepted proof can have no same-erased-transcript canonical
replacement. Constant true is permitted by the original arbitrary-d API. -/
theorem accepted_no_canonical_transcript (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (root : State) :
    let pf : LiteralProtocol.Proof := fun _ => .initial root (fun _ => 0)
    (eval H (verifier D (fun _ _ => true) pub pf)).2 = true ∧
      ∀ pf' : LiteralProtocol.Proof, LiteralTranscript.valid 31 (pf' 31) →
        LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf' 33) ≠
          LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf 33) := by
  dsimp only
  constructor
  · rw [RawCutProverCompiler.verifier, FS2.verifier_eval]
    rfl
  · intro pf' valid same
    exact valid31_not_initial (pf' 31) root valid
      (erased_transcript_row D H pub pf' _ 31 (by decide) same)

/-- This is the requested arbitrary-P reduction law, and it is false even
when erasure equality is required only on accepted executions. -/
theorem no_universal_canonical_reduction (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (root : State) :
    ¬ ∃ transform : Prover → Prover,
      ∀ P : Prover,
        FS2.accepts (eval H (original D (fun _ _ => true) P)) →
        (∀ i, i < 33 → LiteralTranscript.valid i ((eval H (transform P)).2.2 i)) ∧
        LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub
          (eval H (transform P)).2.2 33) =
        LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub
          (eval H P).2.2 33) := by
  rintro ⟨transform, law⟩
  let pf : LiteralProtocol.Proof := fun _ => .initial root (fun _ => 0)
  let P : Prover := Program.done (pub, pf)
  have accepted : FS2.accepts (eval H (original D (fun _ _ => true) P)) := by
    change (eval H (original D (fun _ _ => true) P)).2.2 = true
    rw [RawCutProverCompiler.experiment_eval]
    have out : eval H P = ([], (pub, pf)) := rfl
    rw [out]
    exact (accepted_no_canonical_transcript D H pub root).1
  obtain ⟨valid, same⟩ := law P accepted
  exact (accepted_no_canonical_transcript D H pub root).2
    (eval H (transform P)).2.2 (valid 31 (by decide)) same

/-- The accepted extraction-failure event is equal for each oracle and tape. -/
theorem failure_event (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((eval H (recorded D d (canon P))).2.2 = true ∧
      RawRecordedPublicSpendExtractorBin.extract (eval H (recorded D d (canon P))) coins = none) ↔
    ((eval H (recorded D d P)).2.2 = true ∧
      RawRecordedPublicSpendExtractorBin.extract (eval H (recorded D d P)) coins = none) := by
  rw [(R16CanonRecorded.recorded_observations D d P H).2,
    R16CanonRecorded.recorded_extract D d P H coins]

/-- The maintained cost wrapper refines the same witness value; no equality
of arbitrary resource annotations is required or asserted. -/
theorem costed_value (e : RawExtractorCostComposedBin.CostedExtractor)
    (D : LiteralByteProtocol.Decoder) (d : ErasedPrefix → ErasedMessage → Bool)
    (P : Prover) (H : Bytes → State) (coins : GSConcreteByteDecoderBank.RawCoins) :
    (e.eval (eval H (recorded D d (canon P))) coins).1 =
      (e.eval (eval H (recorded D d P)) coins).1 := by
  rw [e.value, e.value, R16CanonRecorded.recorded_extract D d P H coins]

/-- Symbolic R15 composition at the constructed checkpoint. The admission
join is explicit; this theorem does not pretend it is a byte-layout fact. -/
theorem writer_premise_of_checkpoint_acceptance
    (D : LiteralByteProtocol.Decoder) (d : ErasedPrefix → ErasedMessage → Bool)
    (P : Prover) (source : (Bytes → State) → SourceInputs)
    (model_acceptance : ∀ H, FS2.accepts (eval H (original D d P)) →
      R16DecisionQueryModel.verify (source H).data (source H).queryBytes = true) :
    ∀ H, FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j) := by
  intro H accepted q decoded
  exact R16DecisionQueryModel.accepted_writer (source H).data (source H).queryBytes q
    decoded (model_acceptance H accepted)

#print axioms canon_erased_transcript
#print axioms erased_transcript_row
#print axioms accepted_no_canonical_transcript
#print axioms no_universal_canonical_reduction
#print axioms failure_event
#print axioms costed_value
#print axioms writer_premise_of_checkpoint_acceptance
end AspisR1.R1FinalSoundnessBinPerQueryCanon
end

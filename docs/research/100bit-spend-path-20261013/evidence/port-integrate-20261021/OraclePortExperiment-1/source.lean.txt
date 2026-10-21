import OracleDecisionMultiAccounting

/-! Draft oracle carrier. The recorded experiment is the annotation compiler,
not the single self-recording execution. No frozen-parser claim is made here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortExperiment
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler (Prover RunView)
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)

abbrev Decision := OracleDecisionFeasibilityCore.Decision
abbrev pure := OracleDecisionFeasibilityCore.lift
abbrev verifier := OracleDecisionFeasibilityCore.verifier
abbrev original := OracleDecisionFeasibilityCore.original
abbrev compiled (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  OracleDecisionFeasibilityCompiler.compiled D dO
    (BinCompiledRunWordStability.wordsFromRun D) P
abbrev recorded (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  OracleDecisionPrereqStarts.annotated D dO
    (BinCompiledRunWordStability.wordsFromRun D) P

/-- An all-input issued-call obligation, including rejected executions. -/
def Budget (dO : Decision) : Prop :=
  ∀ (H : Bytes → State) p m, (eval H (dO p m)).1.length ≤ 1046

theorem pure_original (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :
    original D (pure d) P = RecordedBinaryExperimentBin.original D d P :=
  OracleDecisionFeasibilityCore.lift_experiment D d P

theorem pure_recorded (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :
    recorded D (pure d) P = RecordedBinaryExperimentBin.recorded D d P :=
  OracleDecisionFeasibilityCompiler.lift_compiled_experiment D d
    (BinCompiledRunWordStability.wordsFromRun D) P

theorem verifier_budget (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (hB : Budget dO) (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) :
    (eval H (verifier D dO pub pf)).1.length ≤ 1161 :=
  OracleDecisionPrereqSampler.verifier_length D dO H pub pf 1046 (hB H _ _)

theorem first_reads (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (hB : Budget dO) (P : Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (recorded D dO P)).1 ≤ Q + 1161 := by
  rw [recorded, OracleDecisionPrereqStarts.annotated,
    OracleDecisionFeasibilityCompiler.firstReads_eq]
  rw [RawCutProverCompiler.experiment_eval]
  have hp := hq H
  have hv := verifier_budget D dO hB H (eval H P).2.1 (eval H P).2.2
  have hr := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (verifier D dO (eval H P).2.1 (eval H P).2.2)).1)
  rw [List.length_append] at hr
  exact hr.trans (Nat.add_le_add hp hv)

theorem starts (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (hB : Budget dO) (P : Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable
      (eval H (recorded D dO P)).1 ≤ Q + 1080 := by
  have hb := OracleDecisionPrereqStarts.recorded_starts D dO
    (BinCompiledRunWordStability.wordsFromRun D) P H Q 1046 (hq H)
    (fun pub pf T => (DecoderQueryAccounting.starts_le_queries _ _ _).trans (hB H _ _))
  exact hb

theorem log_length (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (hB : Budget dO) (P : Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    (eval H (recorded D dO P)).1.length ≤ (Q + 1161) + 1161 :=
  OracleDecisionPrereqLog.bounded_compiled_length D dO
    (BinCompiledRunWordStability.wordsFromRun D) P H Q 1161 (hq H)
    (verifier_budget D dO hB H)

#print axioms pure_original
#print axioms pure_recorded
#print axioms verifier_budget
#print axioms first_reads
#print axioms starts
#print axioms log_length
end AspisR1.OraclePortExperiment
end

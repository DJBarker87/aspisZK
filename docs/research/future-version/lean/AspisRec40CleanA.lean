import AspisRec40Frames
import AspisRec40CallBudget
import AspisRows40Literal

/-! Aspis 40-row clean event, part 1: the full experiment is the recorded
decision experiment; acceptance; copy of `Frozen2StartChargePrefix.same_transcript`. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanA
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-! ## The full experiment is the recorded decision experiment -/

theorem projected_eq_recorded (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    eval H (AspisRec40.HitMass.projected D d P) =
      eval H (AspisRec40.Decision.recorded D (d (eval H P).2.stored)
        (AspisRec40.ChargePrefix.prover P)) := by
  rw [AspisRec40.Decision.recorded, AspisRec40.Decision.annotated,
    AspisRec40.Decision.compiled_experiment_eval, RawCutProverCompiler.experiment_eval,
    AspisRec40.ChargePrefix.prover_eval]
  simp only [AspisRec40.HitMass.projected, AspisRec40.HitMass.annotated,
    AspisRec40.HitMass.recorded, eval_bind, eval, List.append_nil,
    AspisRec40.HitMass.original_eval, AspisRec40.HitMass.compiled_eval, canon_eval,
    AspisRec40.CallBudget.verifier_enrich]
  rfl

theorem recorded_accepts (D : LiteralByteProtocol.Decoder) (dO : OracleDecisionFeasibilityCore.Decision)
    (P : RawCutProverCompiler.Prover) (H : Bytes → State) :
    (eval H (AspisRec40.Decision.recorded D dO P)).2.2 =
      (eval H (AspisRec40.Decision.original D dO P)).2.2 := by
  rw [AspisRec40.Decision.recorded, AspisRec40.Decision.annotated,
    AspisRec40.Decision.compiled_experiment_eval]
  rfl

/-- Copy of `Frozen2StartChargePrefix.same_transcript`. -/
theorem same_transcript (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    (eval H (AspisRec40.HitMass.projected D d P)).2.1 =
      (eval H (AspisRec40.ChargePrefix.charged D P)).2.1 := by
  have hw : BinCompiledRunWordStability.wordsFromRun D (eval H (experiment
      (AspisRec40.ChargePrefix.prover P) (AspisRec40.Decision.verifier D (d (eval H P).2.stored)))) =
      BinCompiledRunWordStability.wordsFromRun D (eval H (AspisRec40.ChargePrefix.base D P)) :=
    AspisRec40.Frames.words_prefix D _ _ H
  have ho : (eval H (experiment
      (AspisRec40.ChargePrefix.prover P) (AspisRec40.Decision.verifier D (d (eval H P).2.stored)))).2.1 =
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1 :=
    AspisRec40.Frames.output_pair D _ _ H
  rw [projected_eq_recorded, AspisRec40.Decision.recorded, AspisRec40.Decision.annotated,
    AspisRec40.Decision.compiled_experiment_eval, AspisRec40.ChargePrefix.charged_eval]
  dsimp only
  rw [hw, ho]

#print axioms projected_eq_recorded
#print axioms recorded_accepts
#print axioms same_transcript

/-- The acceptance of the decision experiment is the terminal decision's output
on the 40-round erased transcript and message 40. -/
theorem original_accepts (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (P : RawCutProverCompiler.Prover)
    (H : Bytes → State) :
    (eval H (AspisRec40.Decision.original D dO P)).2.2 =
      (eval H (OracleDecisionFeasibilityCore.onBytes dO
        ((pr D).transcript H (eval H P).2.1 (eval H P).2.2 40) ((eval H P).2.2 40))).2 := by
  rw [AspisRec40.Decision.original, RawCutProverCompiler.experiment_eval,
    AspisRec40.Decision.verifier_eval]

#print axioms original_accepts

end AspisRec40.CleanA
end

import AspisRec40HitMass
import AspisCharge40
import AspisOneTxDecision
import RawCutWordsFromRunExecutableBin

/-! Aspis 40-row clean event: the DEFINITIONS of the statement (no theorem yet).

* `CheckedAcceptance40`: copy of R1's `OraclePortConsumer.CheckedAcceptance`
  (no collision on the recorded run and acceptance of the original run give the
  checks on the recorded run's rows): R1's `Checks` on 33 rounds → `AspisChecks
  decodePairS` on 40 rounds, R1's 33-row verifier → the 40-row decision verifier.
  This is the shape the clean event takes as its hypothesis from the
  one-transaction game agent (its M9 `fibre_checks`, built from M7 and
  `accepted_checks_aspis`).
* `CleanAcceptedModel40`: copy of `RawRecordedOracleExtractionMassBin.CleanAcceptedModel`:
  R1's `Checks` on 33 rounds → `AspisChecks decodePairS` on 40 rounds, R1's
  `LiteralClassifier.bad` → `AspisAcceptance.bad decodePairS`, 33 → 40.
* `bad40`: copy of `Frozen2StartChargeClean.bad`: `Q + 1161` → `Q + 1111`
  (`CallBudgetAspis.projected_first_reads`), R1's prefix hit → `HitMass.prefixHit`
  with `classifier40 decodePairS`.
* `FinalDecodes`: the rows-33-to-39 part of `Frozen2StartChargeCompletion.Decodes`
  (R1's states rows below 33 only). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanStatement
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1

/-- Copy of `OraclePortConsumer.compiledRows`: 40 rounds of the 40-row protocol. -/
abbrev compiledRows40 (D : LiteralByteProtocol.Decoder) (dO : OracleDecisionFeasibilityCore.Decision)
    (P : RawCutProverCompiler.Prover) (H : Bytes → State) :=
  ((AspisRows40.Protocol.protocol D).transcript H
    (eval H (AspisRec40.Decision.recorded D dO P)).2.1.1
    (eval H (AspisRec40.Decision.recorded D dO P)).2.1.2 40).rounds

/-- Copy of `OraclePortConsumer.CheckedAcceptance`. -/
def CheckedAcceptance40 (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (P : RawCutProverCompiler.Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    ¬ AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision Q (eval H (AspisRec40.Decision.recorded D dO P)) →
    FS2.accepts (eval H (AspisRec40.Decision.original D dO P)) →
    Nonempty (AspisAcceptance.AspisChecks AspisOneTx.decodePairS
      (eval H (AspisRec40.Decision.recorded D dO P)).2.1.1 (compiledRows40 D dO P H))

/-- Copy of `RawRecordedOracleExtractionMassBin.CleanAcceptedModel`. -/
def CleanAcceptedModel40 (D : LiteralByteProtocol.Decoder)
    (exp : RawRecordedOracleExtractionMassBin.Experiment)
    (hit : RawCutProverCompiler.RunView → Prop) : Prop :=
  ∀ H : Bytes → State,
    let run := eval H exp
    run.2.2 = true → ¬ hit run →
      ∃ _checks : AspisAcceptance.AspisChecks AspisOneTx.decodePairS run.2.1.1
        ((AspisRows40.Protocol.protocol D).transcript H run.2.1.1
          (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun run)
            run.2.1.2) 40).rounds,
        ¬ GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS) run.2.1.1 []
          ((AspisRows40.Protocol.protocol D).transcript H run.2.1.1
            (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun run)
              run.2.1.2) 40).rounds

/-- Copy of `Frozen2StartChargeClean.bad`. -/
def bad40 (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover) (Q : Nat)
    (run : RawCutProverCompiler.RunView) : Prop :=
  AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) run ∨
    AspisRec40.HitMass.prefixHit (AspisCharge40.classifier40 AspisOneTx.decodePairS) D P run

/-- Rows 33 to 39 of `Frozen2StartChargeCompletion.Decodes`, for the Aspis
decoder on a run view `v`. -/
def FinalDecodes (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (v : RawCutProverCompiler.RunView) : Prop :=
  ∀ n a, 33 ≤ n → n < 40 → firstCell ((AspisRows40.Protocol.protocol D).chain H
      v.2.1.1 v.2.1.2 n) = some a →
    ∃ own pend g, AspisRows40.FinalStarts.decFinal a (tableBefore emptyTable v.1 a) =
      some (own,pend,g) ∧
      bfollow g (traceFrom v.1 a) own pend (tableBefore emptyTable v.1 a) =
        some ((AspisRows40.Protocol.protocol D).transcript H v.2.1.1 v.2.1.2 n,
          (AspisRows40.Protocol.protocol D).msg v.2.1.2 n,
          (AspisRows40.Protocol.protocol D).chal H v.2.1.1 v.2.1.2 n)

end AspisRec40.CleanStatement
end

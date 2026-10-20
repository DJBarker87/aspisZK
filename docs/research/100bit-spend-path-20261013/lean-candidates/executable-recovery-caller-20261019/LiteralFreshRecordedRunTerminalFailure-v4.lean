import LiteralFreshTerminalFailurePathDomination
import LiteralRecordedRunFailureMassBoundV6

set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralFreshRecordedRunTerminalFailure

open AspisR1.LiteralFreshTerminalFailurePathDomination
open AspisR1.LiteralFreshBankAbortComposition
open AspisR1.LiteralRecordedRunFailureMassBound
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.LiteralAcceptanceTerminal
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSFixedInputDecoderFamily
open AspisWideTower AspisV8R15.ExactTowerBase
open AspisWide.GSConcreteReceivedWordInputs
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.MemoizedProgramLaw
open FS FS2

variable {Aux : Type}

abbrev ChecksFor (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (run : AspisR1.RawCutProverCompiler.RunView) :=
  Checks run.2.1.1
    ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
      (AspisR1.RawCutTranscriptRun.proof
        (wordsFromRun run) run.2.1.2) 33).rounds

def runExtractorFailureAt
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (runAt : LiteralTranscript.Prefix → Aux → AspisR1.RawCutProverCompiler.RunView)
    (checksAt : ∀ P ctx, Option (ChecksFor decoder H (runAt P ctx)))
    (P : LiteralTranscript.Prefix) (ctx : Aux) (coins : RawCoins) : Prop :=
  match checksAt P ctx with
  | none => False
  | some checks =>
      AspisR1.RawCutWordsFromRunExecutable.extractFromRun
        checks.decoded (runAt P ctx) coins = none

def runExtractorFailureMass
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (runAt : LiteralTranscript.Prefix → Aux → AspisR1.RawCutProverCompiler.RunView)
    (checksAt : ∀ P ctx, Option (ChecksFor decoder H (runAt P ctx)))
    (P : LiteralTranscript.Prefix) (ctx : Aux) : ℚ :=
  mean (fun coins : RawCoins =>
    indicator (runExtractorFailureAt decoder H runAt checksAt P ctx coins))

def runBankInputsAt
    (runAt : LiteralTranscript.Prefix → Aux → AspisR1.RawCutProverCompiler.RunView)
    (P : LiteralTranscript.Prefix) (ctx : Aux) : Inputs WideExact 5 :=
  fromWords (initialWordsFromRun (runAt P ctx))
    (fun _ => finalWordFromRun (runAt P ctx))

/-- The fresh-path theorem consumes actual recorded-run failures. The explicit
realization premise connects each completed challenge prefix to its recorded
raw run and 33-row protocol transcript. `checksAt = none` contributes no
accepted extraction failure; when checks exist, the fixed-log theorem bounds
the conditional coin failure by that run's actual bank abort mass. -/
theorem fresh_recorded_run_failure_lt_100
    (choose : LiteralTranscript.Prefix → Aux → LiteralTranscript.Message)
    (update : LiteralTranscript.Prefix → LiteralTranscript.Message → Aux →
      AspisV8R19.MemoizedProgramLaw.View Bytes State
        LiteralTranscript.Challenge → Aux)
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (runAt : LiteralTranscript.Prefix → Aux → AspisR1.RawCutProverCompiler.RunView)
    (checksAt : ∀ P ctx, Option (ChecksFor decoder H (runAt P ctx)))
    (hrealize : ∀ P ctx, P.rounds.length = 33 →
      P.statement = (runAt P ctx).2.1.1 ∧
        P.rounds =
          ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H
            (runAt P ctx).2.1.1
            (AspisR1.RawCutTranscriptRun.proof
              (wordsFromRun (runAt P ctx)) (runAt P ctx).2.1.2) 33).rounds)
    (pub : LiteralTranscript.Public) (ctx : Aux) :
    freshTerminalPathMean choose update
      (runExtractorFailureMass decoder H runAt checksAt) 33
      (FS.emptyPrefix pub) ctx < 1 / (2^100 : ℚ) := by
  apply fresh_terminal_failure_lt_100 choose update
    (runBankInputsAt runAt) (runExtractorFailureMass decoder H runAt checksAt)
    pub ctx
  · intro P ctx' hlen hclean
    cases hc : checksAt P ctx' with
    | none =>
        have hnonneg : 0 ≤ bankAbortMass (runBankInputsAt runAt P ctx') := by
          unfold bankAbortMass AspisV8R19.OracleResampling.mean
          apply div_nonneg
          · apply Finset.sum_nonneg
            intro coins _
            exact indicator_nonneg _
          · positivity
        change mean (fun coins : RawCoins => indicator
          (runExtractorFailureAt decoder H runAt checksAt P ctx' coins)) ≤
          bankAbortMass (runBankInputsAt runAt P ctx')
        have hzero : mean (fun coins : RawCoins => indicator
            (runExtractorFailureAt decoder H runAt checksAt P ctx' coins)) = 0 := by
          apply mean_congr
          intro coins
          simp only [runExtractorFailureAt, hc, indicator_false]
        rw [hzero]
        exact hnonneg
    | some checks =>
        have hr := hrealize P ctx' hlen
        have hno : ¬ GenericNoHit.hitFrom AspisR1.LiteralClassifier.bad
            (runAt P ctx').2.1.1 []
            (((AspisR1.LiteralByteProtocol.protocol decoder).transcript H
              (runAt P ctx').2.1.1
              (AspisR1.RawCutTranscriptRun.proof
                (wordsFromRun (runAt P ctx')) (runAt P ctx').2.1.2) 33).rounds) := by
          intro hh
          apply hclean
          simpa only [hr.1.symm, hr.2.symm] using hh
        have hmass := recorded_run_extractor_none_mass_le_bank_abort
          decoder H (runAt P ctx') checks hno
        simpa [runExtractorFailureMass, runExtractorFailureAt, runBankInputsAt, hc]
          using hmass
  · intro P ctx'
    unfold runExtractorFailureMass
    calc
      mean (fun coins : RawCoins => indicator
          (runExtractorFailureAt decoder H runAt checksAt P ctx' coins))
          ≤ mean (fun _ : RawCoins => (1 : ℚ)) := by
            apply FS.mean_mono
            intro coins
            by_cases hf : runExtractorFailureAt decoder H runAt checksAt P ctx' coins
            · simp [indicator, hf]
            · simp [indicator, hf]
      _ = 1 := mean_const _

#print axioms fresh_recorded_run_failure_lt_100
end AspisR1.LiteralFreshRecordedRunTerminalFailure
end

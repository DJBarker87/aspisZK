import RawRecordedPublicSpendExtractorCompleteness
import LiteralFreshBankAbortComposition
import R1AllAddressFiatShamir

/-! Compose actual memoized-oracle averaging with fresh private extractor
coins. This does not identify shared-ROM sampling with fresh row sampling.
The classifier hit mass and concrete accepted-model refinement remain named
inputs; no query factor or collision term is discarded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawRecordedOracleExtractionMass
open FS FS2
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.LiteralFreshBankAbortComposition
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.AdaptiveFirstReadLaw

attribute [local instance] Classical.propDecidable
attribute [local irreducible] RawRecordedPublicSpendExtractor.extract
  GSConcreteByteDecoderBank.failed LiteralClassifier.bad

abbrev Experiment := Program Bytes State ((LiteralTranscript.Public ×
  (Nat → LiteralTranscript.Message)) × Bool)

/-- Acceptance in the chosen concrete experiment must establish terminal
checks and the matching no-hit statement for this exact recorded run. The
observable `hit` must be refined to that classifier event; it is not given
fresh-round probabilities by this interface. -/
def CleanAcceptedModel (decoder : LiteralByteProtocol.Decoder)
    (exp : Experiment) (hit : RawCutProverCompiler.RunView → Prop) : Prop :=
  ∀ H : Bytes → State,
    let run := eval H exp
    run.2.2 = true → ¬ hit run →
      ∃ checks : LiteralAcceptanceTerminal.Checks run.2.1.1
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
          (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds,
        ¬ GenericNoHit.hitFrom LiteralClassifier.bad run.2.1.1 []
          ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
            (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds

def failureMass (run : RawCutProverCompiler.RunView) : ℚ :=
  mean (fun coins : GSConcreteByteDecoderBank.RawCoins =>
    indicator (run.2.2 = true ∧ RawRecordedPublicSpendExtractor.extract run coins = none))

private theorem failureMass_le_one (run : RawCutProverCompiler.RunView) :
    failureMass run ≤ 1 := by
  unfold failureMass
  apply le_trans (mean_mono ?_) (by rw [mean_const])
  intro coins
  by_cases h : run.2.2 = true ∧ RawRecordedPublicSpendExtractor.extract run coins = none
  <;> simp [indicator, h]

/-- The terminal private-coin failure probability is bounded under the real
lazy memoized oracle law by the classifier hit mass plus the uniform actual
byte-bank abort envelope. This is conditional on CleanAcceptedModel; it makes
no complete source-acceptance or classifier-density claim. -/
theorem shared_oracle_failure_le_hit_add_abort
    (decoder : LiteralByteProtocol.Decoder) (exp : Experiment)
    (hit : RawCutProverCompiler.RunView → Prop)
    (hmodel : CleanAcceptedModel decoder exp hit) :
    lazyMean exp emptyTable failureMass ≤
      lazyMean exp emptyTable (fun run => indicator (hit run)) +
        (1 / (2 : ℚ)^126) := by
  have hpoint : ∀ H : Bytes → State,
      failureMass (eval H exp) ≤ indicator (hit (eval H exp)) +
        (1 / (2 : ℚ)^126) := by
    intro H
    let run := eval H exp
    change failureMass run ≤ indicator (hit run) + (1 / (2 : ℚ)^126)
    by_cases hh : hit run
    · have hle := failureMass_le_one run
      have hpos : (0 : ℚ) ≤ 1 / (2 : ℚ)^126 := by positivity
      simpa only [indicator, if_pos hh] using
        hle.trans (le_add_of_nonneg_right hpos)
    · by_cases ha : run.2.2 = true
      · obtain ⟨checks, hno⟩ := hmodel H ha hh
        have hle : failureMass run ≤ bankAbortMass
            (AspisWide.GSConcreteReceivedWordInputs.fromWords (initialWordsFromRun run)
              (fun _ => finalWordFromRun run)) := by
          apply mean_mono
          intro coins
          apply indicator_mono
          rintro ⟨_, hf⟩
          by_contra hb
          obtain ⟨w, hw, _⟩ :=
            RawRecordedPublicSpendExtractor.extract_of_checks_noHit_bank
              decoder H run checks hno coins hb
          rw [hf] at hw
          cases hw
        have hb := bankAbortMass_le
          (AspisWide.GSConcreteReceivedWordInputs.fromWords (initialWordsFromRun run)
            (fun _ => finalWordFromRun run))
        simpa only [indicator, if_neg hh, zero_add] using hle.trans hb
      · have hz : failureMass run = 0 := by
          unfold failureMass
          simp [ha, indicator]
        rw [show failureMass (eval H exp) = 0 from hz]
        simp only [show ¬ hit (eval H exp) from hh, indicator, if_false, zero_add]
        positivity
  calc
    _ ≤ lazyMean exp emptyTable (fun run => indicator (hit run) +
        (1 / (2 : ℚ)^126)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval exp _ _ hpoint
    _ = _ := by rw [lazyMean_add, lazyMean_const]

/-- Any actual shared-ROM classifier-hit bound transfers unchanged, with
only the independent extractor-abort envelope added. In particular this
lemma does not replace a query-dependent bound by a 33-round bound. -/
theorem shared_oracle_failure_le_supplied_hit_bound
    (decoder : LiteralByteProtocol.Decoder) (exp : Experiment)
    (hit : RawCutProverCompiler.RunView → Prop)
    (hmodel : CleanAcceptedModel decoder exp hit) (bound : ℚ)
    (hhit : lazyMean exp emptyTable (fun run => indicator (hit run)) ≤ bound) :
    lazyMean exp emptyTable failureMass ≤ bound + (1 / (2 : ℚ)^126) :=
  (shared_oracle_failure_le_hit_add_abort decoder exp hit hmodel).trans
    (add_le_add hhit le_rfl)

#print axioms shared_oracle_failure_le_hit_add_abort
#print axioms shared_oracle_failure_le_supplied_hit_bound
end AspisR1.RawRecordedOracleExtractionMass
end

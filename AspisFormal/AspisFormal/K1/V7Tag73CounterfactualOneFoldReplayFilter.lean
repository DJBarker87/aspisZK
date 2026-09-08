import AspisFormal.K1.V7Tag73CounterfactualOneFoldProviderCore
import AspisFormal.K1.V7Tag73ExactPlainRomRun

/-!
# One-fold providers from literal scheduler-native replay

The causal one-fold theorem needs one total parsed-proof family over every
counterfactual alpha.  This leaf constructs that family directly from the
literal result-carrying plain-ROM scheduler run.  Failed runs and returned
proofs with the wrong fixed gamma or wrong alpha-specialized schedule are
mapped to `none`.

Consequently both coherence properties required by
`CounterfactualParsedOneFoldOracle` are theorems of an executable filter.
They are not caller-provided source assumptions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CounterfactualOneFoldReplayFilter

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Expose a parsed proof only from a normally completed literal scheduler
run whose fixed gamma and alpha-specialized one-fold schedule are exact. -/
noncomputable def plainRomProofAtFoldAlpha?
    {TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) (alpha : QM31Exact)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result)) : Option Tag73K12ParsedProof := by
  classical
  exact match run.terminal with
    | .failed _ => none
    | .returned (.initialFailure _) => none
    | .returned (.completed root _) =>
        let proof := root.adversaryValue.1.publicProof.proof.rawProof
        if proof.gamma = gamma then
          if proof.schedule = scheduleAtAlpha baseSchedule alpha then
            some proof
          else none
        else none

/-- Every proof exposed by the executable filter has the fixed pre-alpha
gamma. -/
theorem plainRomProofAtFoldAlpha_gammaExact
    {TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) (alpha : QM31Exact)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (proof : Tag73K12ParsedProof)
    (proofExact : plainRomProofAtFoldAlpha? gamma baseSchedule alpha run =
      some proof) :
    proof.gamma = gamma := by
  cases terminalExact : run.terminal with
  | failed reason =>
      simp [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
  | returned returnedValue =>
      cases returnedValue with
      | initialFailure failure =>
          simp [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
      | completed root clientRun =>
          simp only [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
          split at proofExact
          next gammaExact =>
            split at proofExact
            next scheduleExact =>
              exact Option.some.inj proofExact ▸ gammaExact
            next scheduleMismatch => simp at proofExact
          next gammaMismatch => simp at proofExact

/-- Every proof exposed by the executable filter has exactly the schedule
obtained by replacing only the fixed schedule's alpha. -/
theorem plainRomProofAtFoldAlpha_scheduleExact
    {TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) (alpha : QM31Exact)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (proof : Tag73K12ParsedProof)
    (proofExact : plainRomProofAtFoldAlpha? gamma baseSchedule alpha run =
      some proof) :
    proof.schedule = scheduleAtAlpha baseSchedule alpha := by
  cases terminalExact : run.terminal with
  | failed reason =>
      simp [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
  | returned returnedValue =>
      cases returnedValue with
      | initialFailure failure =>
          simp [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
      | completed root clientRun =>
          simp only [plainRomProofAtFoldAlpha?, terminalExact] at proofExact
          split at proofExact
          next gammaExact =>
            split at proofExact
            next scheduleExact =>
              exact Option.some.inj proofExact ▸ scheduleExact
            next scheduleMismatch => simp at proofExact
          next gammaMismatch => simp at proofExact

/-- A literal completed return satisfying both checked equalities is exposed
as exactly its production parsed proof. -/
theorem plainRomProofAtFoldAlpha_of_completed
    {TapeIdentity Statement Payload Result : Type}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) (alpha : QM31Exact)
    (run : SchedulerNativeRun
      (SchedulerNativePlainRomResult TapeIdentity Statement
        Tag73K12ParsedProof Payload Result))
    (root : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (returned : run.terminal = .returned (.completed root clientRun))
    (gammaExact : root.adversaryValue.1.publicProof.proof.rawProof.gamma =
      gamma)
    (scheduleExact : root.adversaryValue.1.publicProof.proof.rawProof.schedule =
      scheduleAtAlpha baseSchedule alpha) :
    plainRomProofAtFoldAlpha? gamma baseSchedule alpha run =
      some root.adversaryValue.1.publicProof.proof.rawProof := by
  simp [plainRomProofAtFoldAlpha?, returned, gammaExact, scheduleExact]

/-- Construct the complete causal one-fold parsed-proof oracle from one
literal scheduler replay family. -/
def counterfactualParsedOneFoldOracleOfPlainRomReplay
    {TapeIdentity Statement Payload Result : Type}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule)
    (defaultFinal : FinalMessage QM31Exact)
    (replay : SuccessfulTag73DuplexOrdinaryAttempt →
      SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result)) :
    CounterfactualParsedOneFoldOracle words gamma baseSchedule where
  defaultFinal := defaultFinal
  proof? := fun sample =>
    plainRomProofAtFoldAlpha? gamma baseSchedule
      (successfulDuplexOrdinaryValue sample) (replay sample)
  proofGammaExact := by
    intro sample proof proofExact
    exact plainRomProofAtFoldAlpha_gammaExact gamma baseSchedule
      (successfulDuplexOrdinaryValue sample) (replay sample) proof proofExact
  proofScheduleExact := by
    intro sample proof proofExact
    exact plainRomProofAtFoldAlpha_scheduleExact gamma baseSchedule
      (successfulDuplexOrdinaryValue sample) (replay sample) proof proofExact

/-- The constructed family contains the actual production parsed proof once
the reconstructed tape is shown to return the literal completed run. -/
theorem plainRomReplayOracle_actualProof
    {TapeIdentity Statement Payload Result : Type}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (gamma : QM31Exact) (baseSchedule : ExactSchedule)
    (defaultFinal : FinalMessage QM31Exact)
    (replay : SuccessfulTag73DuplexOrdinaryAttempt →
      SchedulerNativeRun
        (SchedulerNativePlainRomResult TapeIdentity Statement
          Tag73K12ParsedProof Payload Result))
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (root : SchedulerNativePlainRomRootRuntime TapeIdentity Statement
      Tag73K12ParsedProof Payload)
    (clientRun : ConcreteRestorationClientRun Statement Tag73K12ParsedProof
      Payload Result)
    (returned : (replay sample).terminal =
      .returned (.completed root clientRun))
    (gammaExact : root.adversaryValue.1.publicProof.proof.rawProof.gamma =
      gamma)
    (scheduleExact : root.adversaryValue.1.publicProof.proof.rawProof.schedule =
      scheduleAtAlpha baseSchedule (successfulDuplexOrdinaryValue sample)) :
    (counterfactualParsedOneFoldOracleOfPlainRomReplay
      (words := words) gamma baseSchedule defaultFinal replay).proof? sample =
        some root.adversaryValue.1.publicProof.proof.rawProof := by
  exact plainRomProofAtFoldAlpha_of_completed gamma baseSchedule
    (successfulDuplexOrdinaryValue sample) (replay sample) root clientRun
    returned gammaExact scheduleExact

#print axioms plainRomProofAtFoldAlpha_gammaExact
#print axioms plainRomProofAtFoldAlpha_scheduleExact
#print axioms plainRomProofAtFoldAlpha_of_completed
#print axioms counterfactualParsedOneFoldOracleOfPlainRomReplay
#print axioms plainRomReplayOracle_actualProof

end
end AspisK1.V7Tag73CounterfactualOneFoldReplayFilter

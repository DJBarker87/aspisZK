import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.K1.V7Tag73CausalRestoredFamily
import AspisFormal.K1.V7Tag73RestoredPointCompatibleK14

/-!
# K1.4 restored-family failure membership

This algebra-only leaf converts a concrete width-29 failure into membership in
the finite target of a pre-fixed restored response family.  Scheduler and
source replay stay outside this theorem so their large dependent witnesses are
not eliminated twice.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73K14FamilyFailureMembership

open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Once a pre-fixed family is available and selects the concrete failing
candidate, the challenge belongs to that family's width-29 bad set. -/
theorem width29_failure_mem_restored_family_target
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact}
    {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (family : RestoredSelectedChainFamily decoder words)
    (failure : Width29DecompositionFailure decoder words gamma disclosedFinal
      schedule)
    (gammaNonzero : gamma ≠ 0)
    (available : family.available gamma)
    (selectedExact : family.selected gamma = Classical.choose failure) :
    gamma ∈ width29GoodChallenges decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (width29BadStrategy decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
          family.response)) := by
  classical
  let selected := Classical.choose failure
  have selectedFacts := Classical.choose_spec failure
  have selectedWitness := selectedFacts.1
  have noMatching := selectedFacts.2
  have responseAt : family.response gamma = selected.1 := by
    calc
      family.response gamma = (family.selected gamma).1 :=
        family.responseAt gamma available
      _ = selected.1 := by simpa only [selected] using congrArg Prod.fst selectedExact
  have fixedMember : gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
          (extractedWidth29InitialWords words)
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords words) selected)) := by
    rw [mem_width29BadStrategy_good_iff]
    refine ⟨gammaNonzero, ?_, noMatching⟩
    exact selected_chain_yields_valid_width29_response decoder words gamma
      disclosedFinal schedule selected selectedWitness
  rw [mem_width29BadStrategy_good_iff] at fixedMember ⊢
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder
    (extractedWidth29InitialWords words) selected family.response gamma responseAt
  have restoredValid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response) gamma := by
    constructor
    · rw [supportEq]
      exact fixedMember.2.1.1
    · intro index member
      rw [supportEq] at member
      have fixedAgreement := fixedMember.2.1.2 index member
      rw [restoredWidth29Strategy_candidate, responseAt]
      rw [selectedCandidateStrategy_candidate] at fixedAgreement
      exact fixedAgreement
  have restoredNoMatching : ¬ HasMatchingWidth29Decomposition
      decoder.initialEncoder (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response) gamma := by
    intro restoredMatching
    apply fixedMember.2.2
    rcases restoredMatching with ⟨components, shared, onCurve⟩
    refine ⟨components, ?_, ?_⟩
    · rw [← supportEq]
      exact shared
    · unfold Width29CandidateOnCurve at onCurve ⊢
      rw [restoredWidth29Strategy_candidate, responseAt] at onCurve
      rw [selectedCandidateStrategy_candidate]
      exact onCurve
  exact ⟨fixedMember.1, restoredValid, restoredNoMatching⟩

#print axioms width29_failure_mem_restored_family_target

end
end AspisK1.V7Tag73K14FamilyFailureMembership

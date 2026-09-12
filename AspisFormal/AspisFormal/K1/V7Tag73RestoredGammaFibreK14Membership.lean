import AspisFormal.K1.V7Tag73RestoredGammaFibreK14Target

/-!
# Algebraic membership for the compact restored-gamma target

The compiler provenance carrier is compiled in the preceding leaf.  This
leaf sees only its compact algebraic projection and proves membership in the
finite width-29 bad-challenge set.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73RestoredGammaFibreK14Membership

open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73K14FamilyFailureMembership
open AspisK1.V7Tag73RestoredPointCompatibleK14
open AspisK1.V7Tag73RestoredGammaFibreK14Target
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- Package pointwise factor membership into the successful-prefix event
without unfolding that event in source-heavy consumers. -/
theorem successful_gamma_prefix_mem_k14_of_factored
    (flat : AspisK1.V7Tag73VariablePrefixGammaSampler.SuccessfulGammaPrefixTape)
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (member : (AspisK1.V7Tag73VariablePrefixGammaFlatRouting.successfulGammaPrefixFactorization
      flat).2.1 ∈ target
        (AspisK1.V7Tag73VariablePrefixGammaFlatRouting.successfulGammaPrefixFactorization
          flat).1) :
    flat ∈ successfulGammaPrefixSkeletonDependentEventK14 target :=
  member

/-- Source-facing packaging through an arbitrary residual/gamma coordinate
equivalence. -/
theorem mem_preimage_dependent_k14_of_factored
    {Tape Residual : Type}
    (coordinates : Tape ≃ Residual ×
      AspisK1.V7Tag73VariablePrefixGammaSampler.TotalGammaDuplexTape)
    (tape : Tape)
    (target : Residual → VariableGammaCompleteSkeleton → Finset QM31Exact)
    (success : AspisK1.V7Tag73VariablePrefixGammaSampler.GammaPrefixSucceeds
      (coordinates tape).2)
    (member :
      (AspisK1.V7Tag73VariablePrefixGammaFlatRouting.successfulGammaPrefixFactorization
        (⟨(coordinates tape).2, success⟩ :
          AspisK1.V7Tag73VariablePrefixGammaSampler.SuccessfulGammaPrefixTape)).2.1 ∈
        target (coordinates tape).1
          (AspisK1.V7Tag73VariablePrefixGammaFlatRouting.successfulGammaPrefixFactorization
            (⟨(coordinates tape).2, success⟩ :
              AspisK1.V7Tag73VariablePrefixGammaSampler.SuccessfulGammaPrefixTape)).1) :
    tape ∈ coordinates ⁻¹'
      AspisK1.V7Tag73SuccessfulSamplerConditioningBridge.dependentSuccessfulSubtypeEvent
        AspisK1.V7Tag73VariablePrefixGammaSampler.GammaPrefixSucceeds
        (fun residual => successfulGammaPrefixSkeletonDependentEventK14
          (target residual)) :=
  ⟨success, successful_gamma_prefix_mem_k14_of_factored _ _ member⟩

/-- A retained compact failure is in the exact target selected before gamma. -/
theorem restored_gamma_fibre_target_mem_of_branch
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {skeleton : VariableGammaCompleteSkeleton}
    {gamma : QM31Exact}
    (provider : RestoredSelectedBranchProvider decoder words)
    (target : RestoredGammaFibreK14TargetWitness decoder words gamma)
    (branchExact : provider.branch gamma = some target.branch) :
    gamma ∈ variablePrefixK14FailureGammaTarget
      (fun _ => provider) skeleton := by
  rcases target with ⟨nonzero, branch, failure, chosenExact⟩
  have selected := k13_family_selected_of_branch provider gamma branch
    branchExact
  let family := restoredSelectedChainFamilyOfK13Provider provider
  have available : family.available gamma := by
    simpa only [family] using selected.1
  have selectedExact : family.selected gamma = Classical.choose failure := by
    simpa only [family] using selected.2.trans chosenExact
  let chosen := Classical.choose failure
  have chosenFacts := Classical.choose_spec failure
  have responseAt : family.response gamma = chosen.1 := by
    calc
      family.response gamma = (family.selected gamma).1 :=
        family.responseAt gamma available
      _ = chosen.1 := by
        simpa only [chosen] using congrArg Prod.fst selectedExact
  have fixedMember : gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words)
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
          (extractedWidth29InitialWords words)
          (selectedCandidateStrategy decoder
            (extractedWidth29InitialWords words) chosen)) := by
    rw [mem_width29BadStrategy_good_iff]
    refine ⟨nonzero, ?_, chosenFacts.2⟩
    exact selected_chain_yields_valid_width29_response decoder words gamma
      branch.disclosedFinal branch.schedule chosen chosenFacts.1
  rw [mem_width29BadStrategy_good_iff] at fixedMember
  unfold variablePrefixK14FailureGammaTarget
  rw [mem_width29BadStrategy_good_iff]
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder
    (extractedWidth29InitialWords words) chosen family.response gamma responseAt
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

#print axioms restored_gamma_fibre_target_mem_of_branch
#print axioms successful_gamma_prefix_mem_k14_of_factored
#print axioms mem_preimage_dependent_k14_of_factored

end
end AspisK1.V7Tag73RestoredGammaFibreK14Membership

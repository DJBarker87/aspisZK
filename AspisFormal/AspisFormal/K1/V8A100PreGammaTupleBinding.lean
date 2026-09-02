import AspisFormal.V8A100FixedTupleFingerprint
import AspisFormal.K1.V7Tag73CausalRestoredFamily
import AspisFormal.K1.V7Tag73SchedulerNativePreGammaFamily

/-!
# Exact boundary of the V8 pre-gamma tuple-binding argument

The current source pipeline constructs a restoration-wide K1.3 provider from
the exact scheduler replay.  K1.4 coherent extractions, however, live in the
separate `RestoredK14BranchProvider` interface.  No current theorem constructs
that latter provider from every legal compiler continuation; the selected
source bridge proves only the actual-gamma branch and explicitly leaves
cached/advance replay outside the fresh-only scheduler.

This file states that missing interface exactly and proves everything after
it.  It does not postulate an axiom and does not claim that the exact compiler
supplies the structure.  A future source theorem must construct
`ExactCompilerPreGammaTupleObligation` with `sourceFamily` instantiated by
`exactCompilerRestoredSelectedProvider`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V8A100PreGammaTupleBinding

open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6Width29CorrelatedAgreement
open AspisV8A100FixedTupleFingerprint
open AspisV8A100TwoPointDeep

/-- Focused copy of the already established K1.5 family-membership bridge.
Keeping it local avoids importing the large K1.5 classifier merely to use
this small deterministic fact. -/
theorem extraction_components_mem_fixedWidth29TupleList
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) :
    extraction.components ∈ fixedWidth29TupleList decoder
      (extractedWidth29InitialWords words) := by
  have valid := selected_chain_yields_valid_width29_response decoder words
    gamma disclosedFinal schedule extraction.combined
      extraction.combinedSelected
  have shared :
      (selectedCandidateStrategy decoder
        (extractedWidth29InitialWords words) extraction.combined).support gamma ⊆
      width29JointAgreementSet exactInitialEncoder
        (extractedWidth29InitialWords words) extraction.components := by
    simpa only [initialEncoderExact] using extraction.sharedSupport
  exact mem_fixedWidth29TupleList_of_shared_support decoder
    (extractedWidth29InitialWords words) extraction.components
    ((selectedCandidateStrategy decoder
      (extractedWidth29InitialWords words) extraction.combined).support gamma)
    valid.1 shared extraction.everyComponentDecoded

/-- The two parameters and complete component-wise values absorbed before
gamma in the proposed V8 transcript. -/
structure V8TwoPointComponentPrefix where
  parameter0 : QM31Exact
  parameter1 : QM31Exact
  vector0 : Fin 29 → QM31Exact
  vector1 : Fin 29 → QM31Exact
  finite0 : circleDenominator parameter0 ≠ 0
  finite1 : circleDenominator parameter1 ≠ 0

/-- Every available K1.4 continuation consumes the same proof-carried prefix.
This is the semantic conclusion that parsing plus replay must establish; it
is stronger than merely asserting that the values occur somewhere in a raw
history. -/
def RestoredK14ProviderMatchesTwoPointPrefix
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : RestoredK14BranchProvider decoder binding words)
    (componentPrefix : V8TwoPointComponentPrefix) : Prop :=
  ∀ (gamma : QM31Exact)
    (branch : RestoredK14Branch decoder binding words gamma),
    provider.branch gamma = some branch →
      componentOodVector branch.extraction.components
          componentPrefix.parameter0 = componentPrefix.vector0 ∧
        componentOodVector branch.extraction.components
          componentPrefix.parameter1 = componentPrefix.vector1

/-- Exact refinement needed between the compiler-derived K1.3 family and a
restoration-wide K1.4 family.  It rules out a caller-created extraction family
unrelated to the executable source replay. -/
structure RestoredK14ProviderRefinesK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (k13 : RestoredSelectedBranchProvider decoder words)
    (k14 : RestoredK14BranchProvider decoder binding words) : Prop where
  branchRefines : ∀ (gamma : QM31Exact)
    (later : RestoredK14Branch decoder binding words gamma),
    k14.branch gamma = some later →
      ∃ earlier : RestoredSelectedBranch decoder words gamma,
        k13.branch gamma = some earlier ∧
          earlier.selected = later.extraction.combined

/-- **The precise unclosed source theorem conclusion.**

For the production proof this structure must be built with `sourceFamily`
definitionally equal to the `exactCompilerRestoredSelectedProvider` obtained
from one source pause and nuisance skeleton.  The current repository has no
constructor for `k14Family` from that replay, so this is recorded as a data
obligation rather than introduced as a theorem hypothesis under another
name. -/
structure ExactCompilerPreGammaTupleObligation
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (sourceFamily : RestoredSelectedBranchProvider decoder words)
    (componentPrefix : V8TwoPointComponentPrefix) where
  k14Family : RestoredK14BranchProvider decoder binding words
  sourceRefinement :
    RestoredK14ProviderRefinesK13Provider sourceFamily k14Family
  prefixReplay :
    RestoredK14ProviderMatchesTwoPointPrefix k14Family componentPrefix

/-- Once the unclosed source interface is supplied, all available restored
K1.4 branches use one component tuple outside the explicit two-point
collision event. -/
theorem restored_k14_branches_use_one_fixed_tuple
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (provider : RestoredK14BranchProvider decoder binding words)
    (componentPrefix : V8TwoPointComponentPrefix)
    (prefixReplay : RestoredK14ProviderMatchesTwoPointPrefix
      provider componentPrefix)
    (outside : (componentPrefix.parameter0, componentPrefix.parameter1) ∉
      familyTwoPointCollisions
        (fixedWidth29TupleList decoder (extractedWidth29InitialWords words)))
    (leftGamma rightGamma : QM31Exact)
    (left : RestoredK14Branch decoder binding words leftGamma)
    (right : RestoredK14Branch decoder binding words rightGamma)
    (leftExact : provider.branch leftGamma = some left)
    (rightExact : provider.branch rightGamma = some right) :
    left.extraction.components = right.extraction.components := by
  have leftMember := extraction_components_mem_fixedWidth29TupleList
    initialEncoderExact left.extraction
  have rightMember := extraction_components_mem_fixedWidth29TupleList
    initialEncoderExact right.extraction
  have leftVectors := prefixReplay leftGamma left leftExact
  have rightVectors := prefixReplay rightGamma right rightExact
  apply fixedWidth29_eq_of_two_component_vectors decoder
    (extractedWidth29InitialWords words)
    left.extraction.components right.extraction.components
    leftMember rightMember componentPrefix.parameter0 componentPrefix.parameter1
    componentPrefix.finite0 componentPrefix.finite1
  · exact leftVectors.1.trans rightVectors.1.symm
  · exact leftVectors.2.trans rightVectors.2.symm
  · exact outside

/-- The exact missing source structure implies the same fixed-tuple theorem;
the K1.3 refinement field remains available for the later compiler proof even
though deterministic tuple equality itself needs only the K1.4 replay field. -/
theorem exact_obligation_restored_branches_use_one_fixed_tuple
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (sourceFamily : RestoredSelectedBranchProvider decoder words)
    (componentPrefix : V8TwoPointComponentPrefix)
    (obligation : ExactCompilerPreGammaTupleObligation
      (binding := binding) sourceFamily componentPrefix)
    (outside : (componentPrefix.parameter0, componentPrefix.parameter1) ∉
      familyTwoPointCollisions
        (fixedWidth29TupleList decoder (extractedWidth29InitialWords words)))
    (leftGamma rightGamma : QM31Exact)
    (left : RestoredK14Branch decoder binding words leftGamma)
    (right : RestoredK14Branch decoder binding words rightGamma)
    (leftExact : obligation.k14Family.branch leftGamma = some left)
    (rightExact : obligation.k14Family.branch rightGamma = some right) :
    left.extraction.components = right.extraction.components :=
  restored_k14_branches_use_one_fixed_tuple initialEncoderExact
    obligation.k14Family componentPrefix obligation.prefixReplay outside
    leftGamma rightGamma left right leftExact rightExact

#print axioms restored_k14_branches_use_one_fixed_tuple
#print axioms exact_obligation_restored_branches_use_one_fixed_tuple

end AspisK1.V8A100PreGammaTupleBinding

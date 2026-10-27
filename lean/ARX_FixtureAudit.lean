import JFm_Begin
import JFm_ChallengeFixture
import JFm_RealTrace
import JFm_Rounds
import JFn_Nonvacuity
import JFn_TX2
import JFr_ArithmeticFixture
import JFr_TX2_CircleAfterDots
import JFr_TX2_Partial
import JFs_ExactInitialization
import JFs_ExactSerialization
import JFs_PublicDecode
import JFs_PublicFixture
import JFs_PublicValidation
import JFu_AfterstateValidator
import JFu_Installation
import JFv_ClaimsFixture
import JFv_RuntimeWitness
import JFv_SampledFixture
import JFv_SemanticCall
import JFv_SemanticChain
import JFw_RealExpansion
import JFw_TypedPrefix
import JFw_Y1
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Partial fixture predecessors only; no full native pair is claimed.
#check @AspisR1.JFm_ChallengeFixture.inhabited
#print axioms AspisR1.JFm_ChallengeFixture.inhabited
#check @AspisR1.JFm_Begin.source
#print axioms AspisR1.JFm_Begin.source
#check @AspisR1.JFm_RealTrace.source
#print axioms AspisR1.JFm_RealTrace.source
#check @AspisR1.JFm_Rounds.source
#print axioms AspisR1.JFm_Rounds.source
#check @AspisR1.JFn_TX2.partial_on_saved
#print axioms AspisR1.JFn_TX2.partial_on_saved
#check @AspisR1.JFn_Nonvacuity.inhabited
#print axioms AspisR1.JFn_Nonvacuity.inhabited
#check @AspisR1.JFr_ArithmeticFixture.inhabited
#print axioms AspisR1.JFr_ArithmeticFixture.inhabited
#check @AspisR1.JFr_TX2_Partial.on_saved
#print axioms AspisR1.JFr_TX2_Partial.on_saved
#check @AspisR1.JFr_TX2_CircleAfterDots.source
#print axioms AspisR1.JFr_TX2_CircleAfterDots.source
#check @AspisR1.JFs_PublicFixture.inhabited
#print axioms AspisR1.JFs_PublicFixture.inhabited
#check @AspisR1.JFs_PublicDecode.source
#print axioms AspisR1.JFs_PublicDecode.source
#check @AspisR1.JFs_PublicValidation.source
#print axioms AspisR1.JFs_PublicValidation.source
#check @AspisR1.JFs_ExactSerialization.source
#print axioms AspisR1.JFs_ExactSerialization.source
#check @AspisR1.JFs_ExactInitialization.source
#print axioms AspisR1.JFs_ExactInitialization.source
#check @AspisR1.JFu_Installation.extraction
#print axioms AspisR1.JFu_Installation.extraction
#check @AspisR1.JFu_Installation.oracle
#print axioms AspisR1.JFu_Installation.oracle
#check @AspisR1.JFu_AfterstateValidator.source
#print axioms AspisR1.JFu_AfterstateValidator.source
#check @AspisR1.JFv_RuntimeWitness.compatible
#print axioms AspisR1.JFv_RuntimeWitness.compatible
#check @AspisR1.JFv_SampledFixture.inhabited
#print axioms AspisR1.JFv_SampledFixture.inhabited
#check @AspisR1.JFv_ClaimsFixture.inhabited
#print axioms AspisR1.JFv_ClaimsFixture.inhabited
#check @AspisR1.JFv_SemanticCall.success
#print axioms AspisR1.JFv_SemanticCall.success
#check @AspisR1.JFv_SemanticChain.success
#print axioms AspisR1.JFv_SemanticChain.success
#check @AspisR1.JFw_RealExpansion.inhabited
#print axioms AspisR1.JFw_RealExpansion.inhabited
#check @AspisR1.JFw_TypedPrefix.inhabited
#print axioms AspisR1.JFw_TypedPrefix.inhabited
#check @AspisR1.JFw_Y1.inhabited
#print axioms AspisR1.JFw_Y1.inhabited

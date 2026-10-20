import Lean
import FS2.DuplexInj
import FS2.Verifier
import FS2.DuplexTrace
import AllAddressCollision
import AllAddressCollisionTrace
import AspisFormal.CircleFibreRoots
import AspisFormal.CircleGroupOrder
import AspisFormal.CircleGroupCardinality
import AspisFormal.CircleNaturalBasisEval
import AspisFormal.CircleNaturalBasis
import AspisFormal.K1.V7ExactCorrelatedAgreementIncidence
import AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole
import AspisFormal.Pool.KnowledgeExtractorInterface
import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5FriListCap
import AspisFormal.SoundnessLedger
import AspisFormal.V5WithoutReplacementQuerySoundness
import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriJohnsonListBound
import AspisFormal.V6OneFoldParameterAudit
import AspisFormal.V5FunctionalBatching
import AspisFormal.V5FriInitialListBound
import AspisFormal.V5FriNaturalBasisRadix4
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V6Width29CorrelatedAgreement
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement
import AspisFormal.V5FriCircleEncoderDistance
import AspisFormal.V6OneFoldCandidateExtraction
import AspisFormal.V6EncoderDistance

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`FS2.DuplexInj, `FS2.Verifier, `FS2.DuplexTrace, `AllAddressCollision, `AllAddressCollisionTrace, `AspisFormal.CircleFibreRoots, `AspisFormal.CircleGroupOrder, `AspisFormal.CircleGroupCardinality, `AspisFormal.CircleNaturalBasisEval, `AspisFormal.CircleNaturalBasis, `AspisFormal.K1.V7ExactCorrelatedAgreementIncidence, `AspisFormal.K1.V7ExactCorrelatedAgreementWeightedPigeonhole, `AspisFormal.Pool.KnowledgeExtractorInterface, `AspisFormal.V5ComponentCConcreteFoldLinearity, `AspisFormal.V5FriListCap, `AspisFormal.SoundnessLedger, `AspisFormal.V5WithoutReplacementQuerySoundness, `AspisFormal.V5FriCoherentCandidateExtraction, `AspisFormal.V5FriConcreteEncoderCommutation, `AspisFormal.V5FriJohnsonListBound, `AspisFormal.V6OneFoldParameterAudit, `AspisFormal.V5FunctionalBatching, `AspisFormal.V5FriInitialListBound, `AspisFormal.V5FriNaturalBasisRadix4, `AspisFormal.V5FriConcreteEncoderApplicability, `AspisFormal.V6Width29CorrelatedAgreement, `AspisFormal.V5FriDegreeThreeCorrelatedAgreement, `AspisFormal.V5FriCircleEncoderDistance, `AspisFormal.V6OneFoldCandidateExtraction, `AspisFormal.V6EncoderDistance]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

import Lean
import ExtractedPrefixSemanticLow
import ExtractedPrefixCoefficients
import ExtractedPrefixHeaderBytes
import R1RecordLengthCodec
import R1RecordParserModel
import ExtractedPrefixFrameAgreement
import ExtractedPrefixRowPayload
import ExtractedPrefixTypedFull
import FSRetryOutputUniformity
import FieldInterpolationNodes
import FiniteListCandidateMerge
import FiniteOptionSamplerComposition
import FixedInputBankUnionBound
import FoldStoredGeometry
import FoldChildPowers
import FoldD18Commutation
import FoldFactoredDomain
import LineFold
import FoldRuntimeAlgebra
import FoldGeometryBridge
import FoldGeometryAudit
import WideExactGRSInstantiationV5
import GSArrayMatchingCount
import GSNormalizedPointAgreement
import GSWideExactAgreementInputs
import WideExactNaturalBasisComputableV16
import InitialForwardEncoderBaseV9
import RRRootDescent
import RRChildNormalization
import RRActualTaylorSubstitutionV3

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`ExtractedPrefixSemanticLow, `ExtractedPrefixCoefficients, `ExtractedPrefixHeaderBytes, `R1RecordLengthCodec, `R1RecordParserModel, `ExtractedPrefixFrameAgreement, `ExtractedPrefixRowPayload, `ExtractedPrefixTypedFull, `FSRetryOutputUniformity, `FieldInterpolationNodes, `FiniteListCandidateMerge, `FiniteOptionSamplerComposition, `FixedInputBankUnionBound, `FoldStoredGeometry, `FoldChildPowers, `FoldD18Commutation, `FoldFactoredDomain, `LineFold, `FoldRuntimeAlgebra, `FoldGeometryBridge, `FoldGeometryAudit, `WideExactGRSInstantiationV5, `GSArrayMatchingCount, `GSNormalizedPointAgreement, `GSWideExactAgreementInputs, `WideExactNaturalBasisComputableV16, `InitialForwardEncoderBaseV9, `RRRootDescent, `RRChildNormalization, `RRActualTaylorSubstitutionV3]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

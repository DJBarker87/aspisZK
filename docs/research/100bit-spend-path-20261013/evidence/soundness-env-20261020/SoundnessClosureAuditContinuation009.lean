import Lean
import PublicSerializerFieldsRefinement431
import PublicSerializerSuccess431
import PublicSerializerFrontier431
import PublicSerializerWhole431
import PublicExtractedRawBridge431
import WithdrawalValidationAmount431
import WithdrawalCarrierBridge431
import ExtractedPublicCheckedBridge432
import ExtractedAdapterStageBindingObligations
import HchecksPublicComposition
import DecoderInstanceBoundary
import RecordPayloadPartition
import ExtractedPrefixChunkOrder
import ExtractedRecordByteValue
import StrictLowChunkCodec
import ExtractedPrefixFieldAgreement
import ExtractedRecordLimbCanonicality
import ExtractedRecordByteCanonicality
import ExtractedRecordStrictCodec
import ExtractedRecordStrictLow
import ExtractedPrefixLoopMap
import ExtractedPrefixRecordAgreement
import ExtractedPrefixParserAgreement
import ExtractedRecordHighZero
import ExtractedRecordValidator
import ExtractedRecordPayloadSoundness
import ExtractedPrefixRecordStep
import ExtractedPrefixTrace
import ExtractedPrefixParse
import ExtractedPrefixStrictPayload

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`PublicSerializerFieldsRefinement431, `PublicSerializerSuccess431, `PublicSerializerFrontier431, `PublicSerializerWhole431, `PublicExtractedRawBridge431, `WithdrawalValidationAmount431, `WithdrawalCarrierBridge431, `ExtractedPublicCheckedBridge432, `ExtractedAdapterStageBindingObligations, `HchecksPublicComposition, `DecoderInstanceBoundary, `RecordPayloadPartition, `ExtractedPrefixChunkOrder, `ExtractedRecordByteValue, `StrictLowChunkCodec, `ExtractedPrefixFieldAgreement, `ExtractedRecordLimbCanonicality, `ExtractedRecordByteCanonicality, `ExtractedRecordStrictCodec, `ExtractedRecordStrictLow, `ExtractedPrefixLoopMap, `ExtractedPrefixRecordAgreement, `ExtractedPrefixParserAgreement, `ExtractedRecordHighZero, `ExtractedRecordValidator, `ExtractedRecordPayloadSoundness, `ExtractedPrefixRecordStep, `ExtractedPrefixTrace, `ExtractedPrefixParse, `ExtractedPrefixStrictPayload]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

import Lean
import RecordPayloadPartition
import ExtractedPrefixChunkOrder
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
import ExtractedPrefixStrictPayload

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RecordPayloadPartition, `ExtractedPrefixChunkOrder, `ExtractedPrefixFieldAgreement, `ExtractedRecordLimbCanonicality, `ExtractedRecordByteCanonicality, `ExtractedRecordStrictCodec, `ExtractedRecordStrictLow, `ExtractedPrefixLoopMap, `ExtractedPrefixRecordAgreement, `ExtractedPrefixParserAgreement, `ExtractedRecordHighZero, `ExtractedRecordValidator, `ExtractedRecordPayloadSoundness, `ExtractedPrefixStrictPayload]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

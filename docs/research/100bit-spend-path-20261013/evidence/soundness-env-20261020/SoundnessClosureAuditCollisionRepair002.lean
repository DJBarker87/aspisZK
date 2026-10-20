import Lean
import WithdrawalValidationAmount431
import ExtractedRecordByteValue
import StrictLowChunkCodec
import ExtractedPrefixRecordStep
import ExtractedPrefixTrace
import ExtractedPrefixParse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`WithdrawalValidationAmount431, `ExtractedRecordByteValue, `StrictLowChunkCodec, `ExtractedPrefixRecordStep, `ExtractedPrefixTrace, `ExtractedPrefixParse]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

import Lean
import ExtractedSourceFull25Frames
import ExtractedSourceDigestAddresses
import RawSourceDigestLog
import ExtractedSourceSemanticSampler
import ExtractedSourceDigestOracle
import RawSourceLiteralSamplerStep
import RawSourceLiteralTraceLift
import RawSourceGlobalOracleCoupling
import RawSourceGlobalOracleInitial
import RawSamplerSuffixSourceFrames
import RawSamplerSuffixSourceBridge
import BinSourceCommitmentFrames
import BinSourceCommitmentLiteral
import BinSourceCommitmentOpening
import WireTx1PrefixRecords
import WireTx1DigestCalls
import WireTx1OpeningCalls

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`ExtractedSourceFull25Frames, `ExtractedSourceDigestAddresses, `RawSourceDigestLog, `ExtractedSourceSemanticSampler, `ExtractedSourceDigestOracle, `RawSourceLiteralSamplerStep, `RawSourceLiteralTraceLift, `RawSourceGlobalOracleCoupling, `RawSourceGlobalOracleInitial, `RawSamplerSuffixSourceFrames, `RawSamplerSuffixSourceBridge, `BinSourceCommitmentFrames, `BinSourceCommitmentLiteral, `BinSourceCommitmentOpening, `WireTx1PrefixRecords, `WireTx1DigestCalls, `WireTx1OpeningCalls]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

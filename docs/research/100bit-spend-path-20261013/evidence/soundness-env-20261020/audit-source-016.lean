import Lean
import R1SamplerDigits
import R1SamplerArithmetic
import R1SamplerAddBridge
import R1SamplerRanking
import R1SamplerNatModel
import R1SamplerRepeatedPass
import ExtractedQM31SamplerDigits
import ExtractedCurrentQM31Mul
import ExtractedCurrentQM31Tower
import ExtractedCurrentQM31Exact
import ExtractedCurrentQM31Equality
import ExtractedQM31SamplerCarrier
import R1SamplerBlockRank
import R1SamplerByteWord
import R1SamplerBytePass
import R1SourceSamplerByteRank
import ExtractedQM31SamplerCorrect
import ExtractedDigest32SamplerTransport

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1SamplerDigits, `R1SamplerArithmetic, `R1SamplerAddBridge, `R1SamplerRanking, `R1SamplerNatModel, `R1SamplerRepeatedPass, `ExtractedQM31SamplerDigits, `ExtractedCurrentQM31Mul, `ExtractedCurrentQM31Tower, `ExtractedCurrentQM31Exact, `ExtractedCurrentQM31Equality, `ExtractedQM31SamplerCarrier, `R1SamplerBlockRank, `R1SamplerByteWord, `R1SamplerBytePass, `R1SourceSamplerByteRank, `ExtractedQM31SamplerCorrect, `ExtractedDigest32SamplerTransport]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

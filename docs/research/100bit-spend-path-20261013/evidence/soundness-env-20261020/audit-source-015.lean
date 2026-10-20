import Lean
import R0C.CircleRows
import R0P.CircleSampler
import R0P.SemAccept
import R0P.SemHonest
import R0P.SemDeg
import R0P.SemDegFamilies
import R0P.SemVirtualDeg
import R0P.SemPad
import R0C.SlackObstruction
import R0C.SlackBits
import R0C.V3.R0Q
import R0P.MessageDescent
import R0P.SemD3Glue
import R0P.MaskProtocol
import R0P.MaskValue
import BinGrammar
import ExtractedDigest32Transcript
import ExtractedDigest32Callers
import ExtractedDigest32Begin
import R1SamplerLongDivision
import R1SamplerMachineBounds
import R1SamplerWord
import R1SamplerPass
import R1SamplerWordPass
import ExtractedQM31SamplerPass
import ExtractedQM31SamplerPassLoop
import ExtractedQM31SamplerDivision
import ExtractedQM31SamplerBytes
import R1SamplerAddDigits
import R1SamplerCarry

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R0C.CircleRows, `R0P.CircleSampler, `R0P.SemAccept, `R0P.SemHonest, `R0P.SemDeg, `R0P.SemDegFamilies, `R0P.SemVirtualDeg, `R0P.SemPad, `R0C.SlackObstruction, `R0C.SlackBits, `R0C.V3.R0Q, `R0P.MessageDescent, `R0P.SemD3Glue, `R0P.MaskProtocol, `R0P.MaskValue, `BinGrammar, `ExtractedDigest32Transcript, `ExtractedDigest32Callers, `ExtractedDigest32Begin, `R1SamplerLongDivision, `R1SamplerMachineBounds, `R1SamplerWord, `R1SamplerPass, `R1SamplerWordPass, `ExtractedQM31SamplerPass, `ExtractedQM31SamplerPassLoop, `ExtractedQM31SamplerDivision, `ExtractedQM31SamplerBytes, `R1SamplerAddDigits, `R1SamplerCarry]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

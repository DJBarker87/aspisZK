import Lean
import AspisR1Qm31SamplerIndex.Funs
import AspisR1TerminalDecoder.Types
import AspisR1TerminalDecoder.FunsExternal
import AspisR1TerminalDecoder.Funs
import AspisV8R15.CircleChord
import AspisV8R15.ExactTowerBase
import AspisV8R15.ExactTowerChord
import AspisV8R15.ExactTowerFinite
import AspisV8R17.QM31WordFormulas
import AspisV8R17.QM31WordResidues
import AspisV8R17.QuadraticTowerOperations
import AspisV8R17.QM31WordTower
import AspisV8R19.QM31SamplerProgram
import AspisV8R19.Q22WordScan
import AspisV8R19.Q22SamplerProgram
import AspisV8R19.SamplerOracleLaws
import AspisV8R19.QM31SamplerInvariants
import AspisV8R19.BoundedSamplerWrapper
import AspisV8R19.GuardedFirstRead
import AspisV8R19.Q22SamplerInvariants
import AspisV8R19.R402Q22IndependentLaw
import AspisV8R19.R406SamplerWordDistribution
import AspisV8R19.R407Q22CandidateKernel
import AspisV8R19.R409Q22Relabeling
import AspisV8R19.R411EqualLegalQueryMass
import AspisV8R19.R412LegalQueryEnumeration
import AspisV8R19.R413GuardedOracleDistance
import AspisV8R19.R417Q22SuccessLaw
import AspisV8R19.R421UniformMasked31Block
import AspisV8R19.R442RejectionAlphabet

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`AspisR1Qm31SamplerIndex.Funs, `AspisR1TerminalDecoder.Types, `AspisR1TerminalDecoder.FunsExternal, `AspisR1TerminalDecoder.Funs, `AspisV8R15.CircleChord, `AspisV8R15.ExactTowerBase, `AspisV8R15.ExactTowerChord, `AspisV8R15.ExactTowerFinite, `AspisV8R17.QM31WordFormulas, `AspisV8R17.QM31WordResidues, `AspisV8R17.QuadraticTowerOperations, `AspisV8R17.QM31WordTower, `AspisV8R19.QM31SamplerProgram, `AspisV8R19.Q22WordScan, `AspisV8R19.Q22SamplerProgram, `AspisV8R19.SamplerOracleLaws, `AspisV8R19.QM31SamplerInvariants, `AspisV8R19.BoundedSamplerWrapper, `AspisV8R19.GuardedFirstRead, `AspisV8R19.Q22SamplerInvariants, `AspisV8R19.R402Q22IndependentLaw, `AspisV8R19.R406SamplerWordDistribution, `AspisV8R19.R407Q22CandidateKernel, `AspisV8R19.R409Q22Relabeling, `AspisV8R19.R411EqualLegalQueryMass, `AspisV8R19.R412LegalQueryEnumeration, `AspisV8R19.R413GuardedOracleDistance, `AspisV8R19.R417Q22SuccessLaw, `AspisV8R19.R421UniformMasked31Block, `AspisV8R19.R442RejectionAlphabet]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

import Lean
import AspisV8Privacy.FiniteGames
import AspisV8R17.AdaptiveOracle
import AspisV8R19.OracleResampling
import AspisV8PairedCommitment.Table
import AspisV8R19.MemoizedProgramLaw
import AspisV8R19.OracleProgramOps
import AspisV8R19.AdaptiveFirstReadLaw
import AspisV8R19.CausalFirstHitUnionBound
import FS.Statement
import FS.LemmaA
import FS.LemmaB
import FS.Theorem
import FS2.Statement
import FS2.LemmaA
import FS2.Theorem
import R0C.V3.BS
import R0C.V3.Gen
import AspisV8R19.OracleFiniteSupport
import R1AllAddressFiatShamir
import AllAddressFiatShamirOutside
import AcceptedAdaptiveFiatShamir
import R1GenericNoHit
import AcceptedAdaptiveMembershipSoundness
import ExtractorPowComplexity
import AspisR1DecodeKFullV10.Types
import DecodeKOptionDiscriminantBridge
import AspisR1DecodeKFullV10.Funs
import R1CandidateFieldParsers
import ActualDecodeKFieldParserTransport
import ActualDecodeKQMParserTransport

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`AspisV8Privacy.FiniteGames, `AspisV8R17.AdaptiveOracle, `AspisV8R19.OracleResampling, `AspisV8PairedCommitment.Table, `AspisV8R19.MemoizedProgramLaw, `AspisV8R19.OracleProgramOps, `AspisV8R19.AdaptiveFirstReadLaw, `AspisV8R19.CausalFirstHitUnionBound, `FS.Statement, `FS.LemmaA, `FS.LemmaB, `FS.Theorem, `FS2.Statement, `FS2.LemmaA, `FS2.Theorem, `R0C.V3.BS, `R0C.V3.Gen, `AspisV8R19.OracleFiniteSupport, `R1AllAddressFiatShamir, `AllAddressFiatShamirOutside, `AcceptedAdaptiveFiatShamir, `R1GenericNoHit, `AcceptedAdaptiveMembershipSoundness, `ExtractorPowComplexity, `AspisR1DecodeKFullV10.Types, `DecodeKOptionDiscriminantBridge, `AspisR1DecodeKFullV10.Funs, `R1CandidateFieldParsers, `ActualDecodeKFieldParserTransport, `ActualDecodeKQMParserTransport]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms name
        logInfo m!"S_AXIOMS {owner} | {name} | {axs.toList}"

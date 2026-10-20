import Lean
import AspisV8R19.R443BoundedRejectionMass
import AspisV8R19.R445InitialBlockRejectionLaw
import AspisV8R19.R572SequentialWordMass
import AspisV8R19.SamplerWrapperPolicies
import AspisV8R19.SamplerFieldDecode
import AspisV8R19.R599CanonicalFieldTuple
import AspisV8R19.SamplerCirclePolicy
import BackgroundAddressMap
import R1TraceTable
import PartialAddressTrace
import BackgroundAddressFollow
import BackgroundAddressRestriction
import R1BackgroundOwnMap
import R1DecoderStateList
import FS2.DuplexWalk
import R1DuplexRewind
import R1DuplexAbsorb
import R1DuplexSeek
import R1DuplexOrder
import R1DuplexPrefixTable
import R0C.Counting
import R0C.QueryCounting
import R0C.QuerySource
import R0C.QuerySampler
import R0C.V3.Q22Law
import R1QueryContinuation
import R1QueryTruncation
import R1QuerySelectedPrefix
import R1QueryStateList
import R1QueryCompletion

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`AspisV8R19.R443BoundedRejectionMass, `AspisV8R19.R445InitialBlockRejectionLaw, `AspisV8R19.R572SequentialWordMass, `AspisV8R19.SamplerWrapperPolicies, `AspisV8R19.SamplerFieldDecode, `AspisV8R19.R599CanonicalFieldTuple, `AspisV8R19.SamplerCirclePolicy, `BackgroundAddressMap, `R1TraceTable, `PartialAddressTrace, `BackgroundAddressFollow, `BackgroundAddressRestriction, `R1BackgroundOwnMap, `R1DecoderStateList, `FS2.DuplexWalk, `R1DuplexRewind, `R1DuplexAbsorb, `R1DuplexSeek, `R1DuplexOrder, `R1DuplexPrefixTable, `R0C.Counting, `R0C.QueryCounting, `R0C.QuerySource, `R0C.QuerySampler, `R0C.V3.Q22Law, `R1QueryContinuation, `R1QueryTruncation, `R1QuerySelectedPrefix, `R1QueryStateList, `R1QueryCompletion]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"

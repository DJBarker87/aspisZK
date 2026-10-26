import Lean
import AspisV8R19.R443BoundedRejectionMass
import AspisV8R19.R445InitialBlockRejectionLaw
import AspisV8R19.R599CanonicalFieldTuple
import AspisV8R15.ExactTowerFinite
import WideTower
import R0C.ModuloField
import R1WideExactLimbCodec
import R1FoldedLeafCodec
import R1MerkleIndexGeometry
import R1FoldedRecoveredWord
import R0.Fold
import R0.PolynomialPair
import R0.ChordDegree
import R0.Dot
import R0.RoundNormalization
import R0.RoundCore
import R0.Round
import R0.LinearDual
import R0.ChordImage
import R0.ChordGeometry
import R0.Chord
import R0.FunctionalWeights
import R0.ResponseSelection
import Wide.JointList
import Wide.Instances
import Wide.MatchedInstances
import R0.ListsResponses
import R0.RootCounts
import R0.OpeningWeights
import R0.OpeningDefinitions
import R0.BadSetBounds
import R0.OpeningAlgebra
import R0.FibreRestoration
import Wide.SubfieldDescent
import R0.Binding
import R0.Ledger
import AspisV8R19.R402Q22IndependentLaw
import AspisV8R19.R407Q22CandidateKernel
import AspisV8R19.R409Q22Relabeling
import AspisV8R19.R411EqualLegalQueryMass
import AspisV8R19.Q22SamplerInvariants
import AspisV8R19.R412LegalQueryEnumeration
import AspisV8R19.R417Q22SuccessLaw
import R0.QueryLaw
import R0FS.Verifier
import R0FS.Protocol
import R0FS.Hypotheses
import FS2.DuplexWalk
import FS2.DuplexDecodes
import R0FS.V2
import R0C.SemStatement
import R0P.Core
import R0P.PoseidonConstants
import R0P.CoreExt
import R0P.Path
import R0P.Poseidon
import R0P.Positivity
import R0P.Value
import R0P.Positive
import R0P.PositivityWired
import R0P.CopyConstants
import R0P.Copy
import R0P.PositivityChain
import R0P.Schedule
import R0P.EmptyRoots
import R0P.Digest
import R0P.Semantics
import R0P.SemSource
import R0P.SemView
import R0P.Sumcheck
import R0P.Zerocheck
import R0P.Occupancy
import R0P.Asset
import R0P.LaneMap
import R0P.SemDecision
import R0P.CopyInputLinks
import R0P.Extraction
import R0P.SemAssembly
import R0P.CopyRegistry
import R0P.LogUpFrac
import R0P.LogUpCompress
import R0P.SemBadSets
import R0P.LogUpAssembly
import R0P.LogUpChain
import R0P.SemClosed
import R0P.SemRounds
import R0P.SemD3
import R0C.SlackStatement
import R0C.QueryCounting
import AspisV8R19.GuardedFirstRead
import AspisV8R19.R413GuardedOracleDistance
import R0C.QuerySource
import R0C.QuerySampler
import R0C.ConcreteSlack
import R0P.SemD2
import R1SelectedChallengeMapCore
import R1UnifiedSamplerPublic
import R1PublicFieldBlockCodec
import R1PublicIndexCodec
import R1PublicIndexListCodec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisV8R19.R443BoundedRejectionMass, `AspisV8R19.R445InitialBlockRejectionLaw, `AspisV8R19.R599CanonicalFieldTuple, `AspisV8R15.ExactTowerFinite, `WideTower, `R0C.ModuloField, `R1WideExactLimbCodec, `R1FoldedLeafCodec, `R1MerkleIndexGeometry, `R1FoldedRecoveredWord, `R0.Fold, `R0.PolynomialPair, `R0.ChordDegree, `R0.Dot, `R0.RoundNormalization, `R0.RoundCore, `R0.Round, `R0.LinearDual, `R0.ChordImage, `R0.ChordGeometry, `R0.Chord, `R0.FunctionalWeights, `R0.ResponseSelection, `Wide.JointList, `Wide.Instances, `Wide.MatchedInstances, `R0.ListsResponses, `R0.RootCounts, `R0.OpeningWeights, `R0.OpeningDefinitions, `R0.BadSetBounds, `R0.OpeningAlgebra, `R0.FibreRestoration, `Wide.SubfieldDescent, `R0.Binding, `R0.Ledger, `AspisV8R19.R402Q22IndependentLaw, `AspisV8R19.R407Q22CandidateKernel, `AspisV8R19.R409Q22Relabeling, `AspisV8R19.R411EqualLegalQueryMass, `AspisV8R19.Q22SamplerInvariants, `AspisV8R19.R412LegalQueryEnumeration, `AspisV8R19.R417Q22SuccessLaw, `R0.QueryLaw, `R0FS.Verifier, `R0FS.Protocol, `R0FS.Hypotheses, `FS2.DuplexWalk, `FS2.DuplexDecodes, `R0FS.V2, `R0C.SemStatement, `R0P.Core, `R0P.PoseidonConstants, `R0P.CoreExt, `R0P.Path, `R0P.Poseidon, `R0P.Positivity, `R0P.Value, `R0P.Positive, `R0P.PositivityWired, `R0P.CopyConstants, `R0P.Copy, `R0P.PositivityChain, `R0P.Schedule, `R0P.EmptyRoots, `R0P.Digest, `R0P.Semantics, `R0P.SemSource, `R0P.SemView, `R0P.Sumcheck, `R0P.Zerocheck, `R0P.Occupancy, `R0P.Asset, `R0P.LaneMap, `R0P.SemDecision, `R0P.CopyInputLinks, `R0P.Extraction, `R0P.SemAssembly, `R0P.CopyRegistry, `R0P.LogUpFrac, `R0P.LogUpCompress, `R0P.SemBadSets, `R0P.LogUpAssembly, `R0P.LogUpChain, `R0P.SemClosed, `R0P.SemRounds, `R0P.SemD3, `R0C.SlackStatement, `R0C.QueryCounting, `AspisV8R19.GuardedFirstRead, `AspisV8R19.R413GuardedOracleDistance, `R0C.QuerySource, `R0C.QuerySampler, `R0C.ConcreteSlack, `R0P.SemD2, `R1SelectedChallengeMapCore, `R1UnifiedSamplerPublic, `R1PublicFieldBlockCodec, `R1PublicIndexCodec, `R1PublicIndexListCodec ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"

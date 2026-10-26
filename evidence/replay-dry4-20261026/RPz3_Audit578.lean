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
import AspisV8R19.DuplexFrames
import AspisV8R19.DuplexFreshPair
import AspisV8R19.SourceDuplexStep
import AspisV8R19.UniformStateFirstHit
import FS2.Duplex
import R1CanonicalByteAddress
import R1CanonicalByteHash
import R1Merkle32Path
import R1MerkleNodeCodec
import R1MerkleTable
import R1MerkleRecovery
import R1Merkle32Leaf
import R1MerkleLeafRecovery
import R1MerkleLeafCodec
import R1MerkleRecordedLog
import FS2.DuplexDecode
import FS2.DuplexDensity
import FS2.DuplexInj
import FS2.Verifier
import FS2.DuplexTrace
import R1ParsedStateCollision
import R1ParsedTargetsCollision
import R1MerkleChildTargets
import R1MerkleRecordedTargets
import R1MerkleTraceInputs
import R1MerkleLogRecovery
import R1CanonicalOracleLog
import R1CanonicalLogInputs
import R1MerkleProgram
import R1CanonicalMerkleProgram
import R1CanonicalMerkleCollision
import R1CanonicalReadCollision
import R1ParsedTargetsFirstHit
import R1ParsedTargetsPrefixHit
import R1CanonicalMerkleRecovery
import R1CanonicalPredictedRecovery
import R1CanonicalFullTraceRecovery
import R1TrailingStateFrame
import R1FixedOffsetTarget
import R1CommitmentRootTargets
import R1PublicInitFrame
import R1CommitmentRootFrames
import R1ThreeCommitmentFullTrace
import R1TraceTable
import R1TraceTableMembership
import R1CanonicalLogMembership
import R1CanonicalLogSeparation
import R1MerkleNodeLookupExt
import R1MerkleNodeRecordUnique
import R1MerkleLeafLookupExt
import R1MerkleLeafRecordUnique
import R1MerkleLogExt
import R1MerkleWalkWitness
import R1RecordedRecoveryWitness
import R1MerkleLogExtension
import R1CanonicalRecoveryStability
import R1CanonicalTableRecovery
import R1InitialFrameNoMerkle
import R1C1BeforeFrameStability
import R1FirstReadCut
import R1C1TableStability
import R1FixedFrameNoMerkle
import R1LaterCommitmentStability
import R1LaterTableStability
import AspisFormal.V5FriBitReverse
import AspisFormal.CircleGroupOrder
import AspisFormal.V5FriExactLineDomains
import AspisFormal.CircleNaturalBasisEval
import AspisFormal.CircleNaturalBasis
import AspisFormal.CircleFibreRoots
import AspisFormal.SoundnessLedger
import AspisFormal.V5FunctionalBatching
import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5FriListCap
import AspisFormal.V5WithoutReplacementQuerySoundness
import AspisFormal.V5FriCoherentCandidateExtraction
import AspisFormal.V5FriConcreteEncoderCommutation
import AspisFormal.V5FriJohnsonListBound
import AspisFormal.V5FriInitialListBound
import AspisFormal.V5FriNaturalBasisRadix4
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.CircleGroupCardinality
import AspisFormal.V5FriCircleEncoderDistance
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V5FriReleasedLineGeometry

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisV8Privacy.FiniteGames, `AspisV8R17.AdaptiveOracle, `AspisV8R19.OracleResampling, `AspisV8PairedCommitment.Table, `AspisV8R19.MemoizedProgramLaw, `AspisV8R19.OracleProgramOps, `AspisV8R19.AdaptiveFirstReadLaw, `AspisV8R19.CausalFirstHitUnionBound, `FS.Statement, `FS.LemmaA, `FS.LemmaB, `FS.Theorem, `FS2.Statement, `FS2.LemmaA, `FS2.Theorem, `AspisV8R19.DuplexFrames, `AspisV8R19.DuplexFreshPair, `AspisV8R19.SourceDuplexStep, `AspisV8R19.UniformStateFirstHit, `FS2.Duplex, `R1CanonicalByteAddress, `R1CanonicalByteHash, `R1Merkle32Path, `R1MerkleNodeCodec, `R1MerkleTable, `R1MerkleRecovery, `R1Merkle32Leaf, `R1MerkleLeafRecovery, `R1MerkleLeafCodec, `R1MerkleRecordedLog, `FS2.DuplexDecode, `FS2.DuplexDensity, `FS2.DuplexInj, `FS2.Verifier, `FS2.DuplexTrace, `R1ParsedStateCollision, `R1ParsedTargetsCollision, `R1MerkleChildTargets, `R1MerkleRecordedTargets, `R1MerkleTraceInputs, `R1MerkleLogRecovery, `R1CanonicalOracleLog, `R1CanonicalLogInputs, `R1MerkleProgram, `R1CanonicalMerkleProgram, `R1CanonicalMerkleCollision, `R1CanonicalReadCollision, `R1ParsedTargetsFirstHit, `R1ParsedTargetsPrefixHit, `R1CanonicalMerkleRecovery, `R1CanonicalPredictedRecovery, `R1CanonicalFullTraceRecovery, `R1TrailingStateFrame, `R1FixedOffsetTarget, `R1CommitmentRootTargets, `R1PublicInitFrame, `R1CommitmentRootFrames, `R1ThreeCommitmentFullTrace, `R1TraceTable, `R1TraceTableMembership, `R1CanonicalLogMembership, `R1CanonicalLogSeparation, `R1MerkleNodeLookupExt, `R1MerkleNodeRecordUnique, `R1MerkleLeafLookupExt, `R1MerkleLeafRecordUnique, `R1MerkleLogExt, `R1MerkleWalkWitness, `R1RecordedRecoveryWitness, `R1MerkleLogExtension, `R1CanonicalRecoveryStability, `R1CanonicalTableRecovery, `R1InitialFrameNoMerkle, `R1C1BeforeFrameStability, `R1FirstReadCut, `R1C1TableStability, `R1FixedFrameNoMerkle, `R1LaterCommitmentStability, `R1LaterTableStability, `AspisFormal.V5FriBitReverse, `AspisFormal.CircleGroupOrder, `AspisFormal.V5FriExactLineDomains, `AspisFormal.CircleNaturalBasisEval, `AspisFormal.CircleNaturalBasis, `AspisFormal.CircleFibreRoots, `AspisFormal.SoundnessLedger, `AspisFormal.V5FunctionalBatching, `AspisFormal.V5ComponentCConcreteFoldLinearity, `AspisFormal.V5FriListCap, `AspisFormal.V5WithoutReplacementQuerySoundness, `AspisFormal.V5FriCoherentCandidateExtraction, `AspisFormal.V5FriConcreteEncoderCommutation, `AspisFormal.V5FriJohnsonListBound, `AspisFormal.V5FriInitialListBound, `AspisFormal.V5FriNaturalBasisRadix4, `AspisFormal.V5FriConcreteEncoderApplicability, `AspisFormal.CircleGroupCardinality, `AspisFormal.V5FriCircleEncoderDistance, `AspisFormal.V5FriInitialCircleEncoderIdentity, `AspisFormal.V5FriReleasedLineGeometry ]
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

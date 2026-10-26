import Lean
import CheckpointBytesQuery
import CheckpointBytesBody
import CheckpointBytesDecodeC5
import CheckpointBytes3Word
import CheckpointBytes3ScalarShape
import CheckpointBytes3WordMath
import CheckpointBytes3KDecode
import CheckpointBytes3EShape
import CheckpointBytes3EDecode
import OraclePortCkptAbiSourceFields
import CheckpointBytes3Namespaces
import R22Stage2LocalBodies
import R22ControlBounds
import R22Stage2ControlBounds
import R22Stage2ReaderTotal
import OraclePortCkptAbiReader
import OraclePortCkptAbiReadSequence
import OraclePortCkptAbi2Unwrap
import CheckpointBytesReaderWidth
import CheckpointBytes3Reader
import OraclePortJoinSplitStd
import OraclePortStdBuilder
import OraclePortCkptAbi2StdInventory
import OraclePortCkptAbi2Vec
import OraclePortCkptAbi3StdInspection
import OraclePortCkptAbi3OwnedIter
import OraclePortStdAllocation
import OraclePortCkptAbi4Std
import OraclePortCkptAbi5Weights
import CheckpointBytes4Sections
import CheckpointBytes4ReaderFields
import CheckpointBytes4FlatSections
import CheckpointBytes4Weights
import CheckpointBytes3Allocation
import CheckpointBytes4Ops
import CheckpointBytes4SemanticFields
import CheckpointBytes4WeightFields
import CheckpointBytes4SectionContents
import CheckpointBytes4RawFields
import CheckpointBytes4Layout
import CheckpointBytes4QueryWord
import CheckpointBytes4QueryDecode
import CheckpointBytes4FixedWidth
import CheckpointBytes4SavedFields
import CheckpointBytes4Next
import CheckpointBytes4Comparison
import CheckpointBytes4SuccessfulFields
import WireTx2BinaryBodies
import WireTx2Records
import CheckpointBytes5Inputs
import CheckpointBytesBodyDecodeJoin
import CheckpointBytes5Writer
import CheckpointBytes5Output
import OraclePortAcceptedContextC6
import OraclePortFrozen2Checkpoint
import OraclePortShortCircuitAccounting
import OraclePortFrozenOrderAccounting
import OraclePortFrozenOrderBounds
import OraclePortFrozenOrderEnvelopes
import OraclePortFrozen2Decision
import OraclePortFrozen2Digests
import OraclePortCkptAbi5Stage
import OraclePortCkptAbi5Decision
import CheckpointBytes5Join
import CheckpointBytes5Decision
import MultiproofConeRef.Types
import MultiproofConeRef.Funs
import MultiproofConeRead32
import MultiproofConeLevelIteration
import MultiproofConeNodeDomain
import MultiproofConeNodeIteration
import MultiproofConeNodeAdoption
import MultiproofConeModelBoundary
import MultiproofConeLiveOrder
import MultiproofConeLiveLeaves
import MultiproofConeLiveReference
import MultiproofConeLivePreservation
import MultiproofConeLeaf
import MultiproofSortRef.Types
import MultiproofSortRef.Funs
import MultiproofConeSortStep
import MultiproofConeSortInsertion
import MultiproofConeSortTotal
import MultiproofConeSortOrder
import MultiproofConeLiveBatch
import MultiproofConePhysicalDigest
import MultiproofConeLiveFold
import MultiproofConeOrderedLevel
import MultiproofConePhysicalProgram
import MultiproofConePhysicalLevels
import MultiproofConePhysicalTransport
import MultiproofConePhysicalAddress
import MultiproofConePhysicalLive
import MultiproofConeSlices
import MultiproofConeNodeWindow
import MultiproofConePhysicalViews
import MultiproofConeLeafContent
import MultiproofConeKeyAdapters
import MultiproofConeOpeningAdapters
import MultiproofConeLeafFold

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `CheckpointBytesQuery, `CheckpointBytesBody, `CheckpointBytesDecodeC5, `CheckpointBytes3Word, `CheckpointBytes3ScalarShape, `CheckpointBytes3WordMath, `CheckpointBytes3KDecode, `CheckpointBytes3EShape, `CheckpointBytes3EDecode, `OraclePortCkptAbiSourceFields, `CheckpointBytes3Namespaces, `R22Stage2LocalBodies, `R22ControlBounds, `R22Stage2ControlBounds, `R22Stage2ReaderTotal, `OraclePortCkptAbiReader, `OraclePortCkptAbiReadSequence, `OraclePortCkptAbi2Unwrap, `CheckpointBytesReaderWidth, `CheckpointBytes3Reader, `OraclePortJoinSplitStd, `OraclePortStdBuilder, `OraclePortCkptAbi2StdInventory, `OraclePortCkptAbi2Vec, `OraclePortCkptAbi3StdInspection, `OraclePortCkptAbi3OwnedIter, `OraclePortStdAllocation, `OraclePortCkptAbi4Std, `OraclePortCkptAbi5Weights, `CheckpointBytes4Sections, `CheckpointBytes4ReaderFields, `CheckpointBytes4FlatSections, `CheckpointBytes4Weights, `CheckpointBytes3Allocation, `CheckpointBytes4Ops, `CheckpointBytes4SemanticFields, `CheckpointBytes4WeightFields, `CheckpointBytes4SectionContents, `CheckpointBytes4RawFields, `CheckpointBytes4Layout, `CheckpointBytes4QueryWord, `CheckpointBytes4QueryDecode, `CheckpointBytes4FixedWidth, `CheckpointBytes4SavedFields, `CheckpointBytes4Next, `CheckpointBytes4Comparison, `CheckpointBytes4SuccessfulFields, `WireTx2BinaryBodies, `WireTx2Records, `CheckpointBytes5Inputs, `CheckpointBytesBodyDecodeJoin, `CheckpointBytes5Writer, `CheckpointBytes5Output, `OraclePortAcceptedContextC6, `OraclePortFrozen2Checkpoint, `OraclePortShortCircuitAccounting, `OraclePortFrozenOrderAccounting, `OraclePortFrozenOrderBounds, `OraclePortFrozenOrderEnvelopes, `OraclePortFrozen2Decision, `OraclePortFrozen2Digests, `OraclePortCkptAbi5Stage, `OraclePortCkptAbi5Decision, `CheckpointBytes5Join, `CheckpointBytes5Decision, `MultiproofConeRef.Types, `MultiproofConeRef.Funs, `MultiproofConeRead32, `MultiproofConeLevelIteration, `MultiproofConeNodeDomain, `MultiproofConeNodeIteration, `MultiproofConeNodeAdoption, `MultiproofConeModelBoundary, `MultiproofConeLiveOrder, `MultiproofConeLiveLeaves, `MultiproofConeLiveReference, `MultiproofConeLivePreservation, `MultiproofConeLeaf, `MultiproofSortRef.Types, `MultiproofSortRef.Funs, `MultiproofConeSortStep, `MultiproofConeSortInsertion, `MultiproofConeSortTotal, `MultiproofConeSortOrder, `MultiproofConeLiveBatch, `MultiproofConePhysicalDigest, `MultiproofConeLiveFold, `MultiproofConeOrderedLevel, `MultiproofConePhysicalProgram, `MultiproofConePhysicalLevels, `MultiproofConePhysicalTransport, `MultiproofConePhysicalAddress, `MultiproofConePhysicalLive, `MultiproofConeSlices, `MultiproofConeNodeWindow, `MultiproofConePhysicalViews, `MultiproofConeLeafContent, `MultiproofConeKeyAdapters, `MultiproofConeOpeningAdapters, `MultiproofConeLeafFold ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"

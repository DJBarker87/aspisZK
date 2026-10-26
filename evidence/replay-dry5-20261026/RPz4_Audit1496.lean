import Lean
import S1ValuesOwnedCellV1
import S1ValuesOwnedChunkFormulaV1
import S1FrameArithmeticV1
import S1ValuesOwnedStepBytesV1
import S1ValuesOwnedChunkBytesV1
import S1ValuesOwnedExpansionFormulaV1
import S1ValuesOwnedChunkTotalV1
import S1ValuesOwnedOuterStepTotalV1
import S1ValuesOwnedExpansionBytesV1
import S1ValuesOwnedReferenceBytesV1
import S1ValuesOwnedOuterTotalV1
import S1ValuesOwnedExactV1
import S1ValuesOwnedAcceptedBytesV1
import S1QueryArrayOperationsV1
import S1QueryOverwriteEightV1
import S2W_SiteSchedule
import S2W_InputSchedule
import S2W_ChildEventPorts
import S2W_TwoFieldAudit
import S2W_DigestExtraction
import S2W_D188Consolidation
import S2W_CommittedCheckpoint
import S2W_AccountObservations
import S2W_D189Interpretation
import S2W_EntryPrivileges
import S2W_ReturnedCheckpoint
import S2W_Snapshot
import S2W_SnapshotFacts
import S2W_SnapshotJoin
import S2W_D189Entry
import S2W_D189Wrappers
import S2W_ExpandedTrace
import S2W_ExpandedChildren
import S2W_OuterOccurrences
import S2W_FirstOccurrence
import S2W_TraceSplice
import S2W_NativeSchedule
import S2W_ScheduledConsolidation
import S2W_D189Consolidation
import SInt2_SdkDependencyFactorV1
import SInt2_S6SdkFirstObjectEquivalenceV1
import SInt2_S6SdkSourceCutTypesV1
import ClaimsUnrolledParentTypes
import ClaimsUnrolledParentSource
import ClaimsUnrolledParentRows
import Port2_QuerySource
import Port2_QueryAdvance
import VTop_Types
import VTop_Model
import VTop_Entry
import VTop_Provenance
import VTop_Cuts
import Port1_LibrarySource
import VTop_Trace
import OraclePortShortCircuitTransport
import OraclePortRefineJoinCore
import OraclePortRefineJoinStrict
import OraclePortFrozenOrderRecoveryStep
import OraclePortFrozenOrderRecoveryLevels
import OraclePortFrozenOrderLeaves
import OraclePortFrozenOrderSlotPath
import OraclePortFrozenOrderCutRecovery
import OraclePortFrozenOrderSelectedRecovery
import OraclePortFrozenOrderChecks
import OraclePortFrozen2Trace
import OraclePortFrozen2Resource
import OraclePortFrozen2Bounds
import OraclePortFrozen2Reached
import OraclePortFrozen2Roots
import OraclePortFrozen2ActualChecks
import OraclePortFrozen2CanonicalChecks
import OraclePortFrozen2C6
import OraclePortFrozen2Consumer
import OraclePortFrozen2Probability
import OraclePortFrozen2Join
import VTop_OracleCode
import VTop_Flow
import VTop_OracleStages
import Port1_Library
import Port1_Driver
import Port1_DriverSubstitution
import Port1_StoredCarrier
import Port1_CanonicalJoin
import Port1_ModelOrder
import Port2_Initial
import Port2_ReturnedState
import Port2_QueryLoop
import Port3_QueryFrame
import ChildJoin_Decoder
import ChildJoin_Checkpoint
import VTop_Checkpoint
import Port3_CheckpointInstall
import Port3_Constants
import Port3_Initial
import Port3_Constructor
import Port3_QueryInstall
import S8JoinFinishExact
import S8JoinFinishField
import Port3_FlushInstall
import Port3_PendingInstall

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `S1ValuesOwnedCellV1, `S1ValuesOwnedChunkFormulaV1, `S1FrameArithmeticV1, `S1ValuesOwnedStepBytesV1, `S1ValuesOwnedChunkBytesV1, `S1ValuesOwnedExpansionFormulaV1, `S1ValuesOwnedChunkTotalV1, `S1ValuesOwnedOuterStepTotalV1, `S1ValuesOwnedExpansionBytesV1, `S1ValuesOwnedReferenceBytesV1, `S1ValuesOwnedOuterTotalV1, `S1ValuesOwnedExactV1, `S1ValuesOwnedAcceptedBytesV1, `S1QueryArrayOperationsV1, `S1QueryOverwriteEightV1, `S2W_SiteSchedule, `S2W_InputSchedule, `S2W_ChildEventPorts, `S2W_TwoFieldAudit, `S2W_DigestExtraction, `S2W_D188Consolidation, `S2W_CommittedCheckpoint, `S2W_AccountObservations, `S2W_D189Interpretation, `S2W_EntryPrivileges, `S2W_ReturnedCheckpoint, `S2W_Snapshot, `S2W_SnapshotFacts, `S2W_SnapshotJoin, `S2W_D189Entry, `S2W_D189Wrappers, `S2W_ExpandedTrace, `S2W_ExpandedChildren, `S2W_OuterOccurrences, `S2W_FirstOccurrence, `S2W_TraceSplice, `S2W_NativeSchedule, `S2W_ScheduledConsolidation, `S2W_D189Consolidation, `SInt2_SdkDependencyFactorV1, `SInt2_S6SdkFirstObjectEquivalenceV1, `SInt2_S6SdkSourceCutTypesV1, `ClaimsUnrolledParentTypes, `ClaimsUnrolledParentSource, `ClaimsUnrolledParentRows, `Port2_QuerySource, `Port2_QueryAdvance, `VTop_Types, `VTop_Model, `VTop_Entry, `VTop_Provenance, `VTop_Cuts, `Port1_LibrarySource, `VTop_Trace, `OraclePortShortCircuitTransport, `OraclePortRefineJoinCore, `OraclePortRefineJoinStrict, `OraclePortFrozenOrderRecoveryStep, `OraclePortFrozenOrderRecoveryLevels, `OraclePortFrozenOrderLeaves, `OraclePortFrozenOrderSlotPath, `OraclePortFrozenOrderCutRecovery, `OraclePortFrozenOrderSelectedRecovery, `OraclePortFrozenOrderChecks, `OraclePortFrozen2Trace, `OraclePortFrozen2Resource, `OraclePortFrozen2Bounds, `OraclePortFrozen2Reached, `OraclePortFrozen2Roots, `OraclePortFrozen2ActualChecks, `OraclePortFrozen2CanonicalChecks, `OraclePortFrozen2C6, `OraclePortFrozen2Consumer, `OraclePortFrozen2Probability, `OraclePortFrozen2Join, `VTop_OracleCode, `VTop_Flow, `VTop_OracleStages, `Port1_Library, `Port1_Driver, `Port1_DriverSubstitution, `Port1_StoredCarrier, `Port1_CanonicalJoin, `Port1_ModelOrder, `Port2_Initial, `Port2_ReturnedState, `Port2_QueryLoop, `Port3_QueryFrame, `ChildJoin_Decoder, `ChildJoin_Checkpoint, `VTop_Checkpoint, `Port3_CheckpointInstall, `Port3_Constants, `Port3_Initial, `Port3_Constructor, `Port3_QueryInstall, `S8JoinFinishExact, `S8JoinFinishField, `Port3_FlushInstall, `Port3_PendingInstall ]
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

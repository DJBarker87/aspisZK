import Lean
import Port3_PushFrame
import Port3_Wrapping
import Port3_NativePendingBody
import Port3_NativePendingStep
import Port3_NativePendingLoop
import Port3_RowsFrame
import Port3_RowsInstall
import Port3_QueryRaw
import Port3_WriterShape
import Port3_NativePendingInstall
import Port3_NativePendingPrefix
import Port3_NativeQueryBody
import Port3_NativeQueryFrame
import Port3_QueryStage
import SdkC_Source
import SdkC_SourceLaws
import SdkC_Oracle
import Port4A_NativeReader
import Port4A_ReaderNormalize
import Port3_NativeBatchBody
import Port3_NativeBatchCalls
import Port3_BatchStd
import Port3_BatchStage
import Port3_NativeGeometryBody
import Port3_GeometryStage
import Stage2FinishBody
import Port3_NativeFinishBody
import Port3_FinishControl
import Port3_FinishStage
import Port3_Parents
import Port3_NativeRowFrame
import Port3_NativeRowLoop
import Port3_NativeQueryRaw
import Port3_NativeWriterShape
import Port3_CheckpointRows
import Port4A_ReaderInstall
import Port5Q2_ReaderRaw
import Port6CK_Roots
import Port6CK_Queries
import Port6CK_Factor
import Port5Q2_ReaderSemantic
import Port5Q2_ReaderScalar
import Port6CK_Semantic
import Port5Q2_ReaderWeights
import Port5Q2_ReaderFrame
import Port5Q2_ReaderWeightJoin
import Port6CK_Weights
import Port5Q2_ReaderPrefix
import Port5Q2_Shift
import Port5Q2_ReaderValidate
import Port6CK_Ops
import Port6CK_Suffix
import Port6CK_QueryFrame
import Port6CK_Tail
import Port6CK_Header
import Port6CK_Reader
import Port8EFF_CheckpointCode
import Port9OR_Reply
import Port9OR_Code
import Port4B_CallerViews
import Port4B_Opening
import Port4B_LeafCode
import Port4B_Cuts
import Port4B_PhysicalCalls
import Port4B_LeafInstall
import Port4B_LeafStep
import Port4B_NativeLeaf
import Port4B_KeyDecode
import Port4B_LeafCut
import Port4B_LeafLoop
import Port4B_Rejection
import Port4B_NativeReject
import Port4B_AcceptedTail
import Port4B_TreeCuts
import Port4B_SortInstall
import Port4B_CountInstall
import Port4B_AnyFalse
import Port4B_ByteWord
import Port4B_PaddingWord
import Port4B_Padding
import Port4B_SlotInstall
import Port4B_TailReads
import Port4B_VerifyInstall
import Port9OR_P6Node
import Port9OR_P6Progress
import Port9OR_P6Rows
import Port9OR_P6Levels
import Port9OR_P6Verify
import Port4B_VerifyRun
import Port4B_SliceReads
import Port4B_Prepared
import Port4B_Capacity
import Port4B_TailRun
import Port4B_Bounds
import Port4B_TreeJoin
import Port4B_BatchJoin
import Port4B_KeyInstall
import Port4B_Install
import Port9OR_BatchStep
import Port9OR_BatchProgress

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `Port3_PushFrame, `Port3_Wrapping, `Port3_NativePendingBody, `Port3_NativePendingStep, `Port3_NativePendingLoop, `Port3_RowsFrame, `Port3_RowsInstall, `Port3_QueryRaw, `Port3_WriterShape, `Port3_NativePendingInstall, `Port3_NativePendingPrefix, `Port3_NativeQueryBody, `Port3_NativeQueryFrame, `Port3_QueryStage, `SdkC_Source, `SdkC_SourceLaws, `SdkC_Oracle, `Port4A_NativeReader, `Port4A_ReaderNormalize, `Port3_NativeBatchBody, `Port3_NativeBatchCalls, `Port3_BatchStd, `Port3_BatchStage, `Port3_NativeGeometryBody, `Port3_GeometryStage, `Stage2FinishBody, `Port3_NativeFinishBody, `Port3_FinishControl, `Port3_FinishStage, `Port3_Parents, `Port3_NativeRowFrame, `Port3_NativeRowLoop, `Port3_NativeQueryRaw, `Port3_NativeWriterShape, `Port3_CheckpointRows, `Port4A_ReaderInstall, `Port5Q2_ReaderRaw, `Port6CK_Roots, `Port6CK_Queries, `Port6CK_Factor, `Port5Q2_ReaderSemantic, `Port5Q2_ReaderScalar, `Port6CK_Semantic, `Port5Q2_ReaderWeights, `Port5Q2_ReaderFrame, `Port5Q2_ReaderWeightJoin, `Port6CK_Weights, `Port5Q2_ReaderPrefix, `Port5Q2_Shift, `Port5Q2_ReaderValidate, `Port6CK_Ops, `Port6CK_Suffix, `Port6CK_QueryFrame, `Port6CK_Tail, `Port6CK_Header, `Port6CK_Reader, `Port8EFF_CheckpointCode, `Port9OR_Reply, `Port9OR_Code, `Port4B_CallerViews, `Port4B_Opening, `Port4B_LeafCode, `Port4B_Cuts, `Port4B_PhysicalCalls, `Port4B_LeafInstall, `Port4B_LeafStep, `Port4B_NativeLeaf, `Port4B_KeyDecode, `Port4B_LeafCut, `Port4B_LeafLoop, `Port4B_Rejection, `Port4B_NativeReject, `Port4B_AcceptedTail, `Port4B_TreeCuts, `Port4B_SortInstall, `Port4B_CountInstall, `Port4B_AnyFalse, `Port4B_ByteWord, `Port4B_PaddingWord, `Port4B_Padding, `Port4B_SlotInstall, `Port4B_TailReads, `Port4B_VerifyInstall, `Port9OR_P6Node, `Port9OR_P6Progress, `Port9OR_P6Rows, `Port9OR_P6Levels, `Port9OR_P6Verify, `Port4B_VerifyRun, `Port4B_SliceReads, `Port4B_Prepared, `Port4B_Capacity, `Port4B_TailRun, `Port4B_Bounds, `Port4B_TreeJoin, `Port4B_BatchJoin, `Port4B_KeyInstall, `Port4B_Install, `Port9OR_BatchStep, `Port9OR_BatchProgress ]
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

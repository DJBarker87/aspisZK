import Lean
import Port9OR_BatchLoop
import Port9OR_BatchTree
import Op3I_Source
import Op3I_Std
import Op3I_Header
import Op3I_ParseLaws
import Port3_FinishAny
import Port4D_Round
import Port3_NativeFlushBody
import Port4D_FlushABI
import Port4D_FlushStep
import Port4D_FlushLoop
import Port4D_FlushResult
import Port4D_FlushRows
import Port4D_Value
import Port4D_FinishInstall
import RowFinish_Control
import Port4D_Pairing
import Port4D_FinishFrozen
import Port4D_ReturnedFinish
import RowFinish_Finalization
import FinT_Comparisons
import FinT_Algebra
import FinT_Returned
import FinT_Pairing
import FinT_Model
import Port3_NativeTerms
import Port3_NativeQueryTerms
import Port4C_QueryValues
import Port4C_QueryStd
import Port4C_QueryArithmetic
import Port5Q1_OpeningValues
import Port4C_GeometryStd
import Port4C_GeometryGather
import Port4C_GeometryControl
import Port4C_GeometryRange
import Port4C_GeometryLoop
import Port4C_GeometryFields
import Port4C_NativePrefix
import Port4C_PrefixMeaning
import Port4C_Reverse
import Port4C_OwnedInverse
import Port4C_InverseLoop
import Port4C_InverseBackend
import Port4C_BatchInverse
import Port4C_InverseExecution
import Port4C_OwnedGeometryInverse
import Port4C_GeometryInverse
import Port4C_FromFn
import Port4C_FromFnFixed
import Port4C_GeometryGroups
import Port4C_CollectStd
import Port4C_CollectLoop
import Port5Q1_GeometryTerminal
import Port5Q1_GeometryCanonical
import Port5Q1_Geometry
import Port5Q1_Domain
import Port5Q1_Gather
import Port5Q1_GeometryModel
import Port5Q1_ListCells
import Port5Q1_GeometryBinding
import Port5Q1_MapPoint
import Port5Q1_SelectedCells
import Port5Q1_GeometryLine
import Port5Q1_FlatPoint
import Port5Q1_WordShape
import Port5Q1_GeometryInverseCells
import Port5Q1_GeometryCells
import Port5Q1_GeometryReads
import Port5Q1_GeometryAccessor
import Port4C_RowStd
import Port4C_RowLoop
import Port4C_RowMeaning
import Port4C_BasisInner
import Port4C_BasisOuter
import Port4C_BasisMeaning
import Port4C_Accumulation
import Port4C_QueryMeaning
import Port4C_QueryLoop
import Port4C_SumField
import Port4C_FlushField
import Port4C_QueryState
import Port4C_FlushState
import Port5Q1_Advance
import Port5Q1_NodeModel
import Port5Q1_QueryPorts
import VTop_Erasure
import VTop_Run
import VTop_SecondFlow
import VTop_SecondOrder
import VTop_Order
import Port5Q1_Parsed
import Port5Q1_FoldedData
import Port5Q1_ObservedOpening
import Port5Q1_InstallPorts
import Port5Q1_FiveCells
import Port5Q1_DomainLanes
import Port5Q1_ObservedGeometry
import Port5Q1_LineModel
import Port5Q1_LineInputs

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `Port9OR_BatchLoop, `Port9OR_BatchTree, `Op3I_Source, `Op3I_Std, `Op3I_Header, `Op3I_ParseLaws, `Port3_FinishAny, `Port4D_Round, `Port3_NativeFlushBody, `Port4D_FlushABI, `Port4D_FlushStep, `Port4D_FlushLoop, `Port4D_FlushResult, `Port4D_FlushRows, `Port4D_Value, `Port4D_FinishInstall, `RowFinish_Control, `Port4D_Pairing, `Port4D_FinishFrozen, `Port4D_ReturnedFinish, `RowFinish_Finalization, `FinT_Comparisons, `FinT_Algebra, `FinT_Returned, `FinT_Pairing, `FinT_Model, `Port3_NativeTerms, `Port3_NativeQueryTerms, `Port4C_QueryValues, `Port4C_QueryStd, `Port4C_QueryArithmetic, `Port5Q1_OpeningValues, `Port4C_GeometryStd, `Port4C_GeometryGather, `Port4C_GeometryControl, `Port4C_GeometryRange, `Port4C_GeometryLoop, `Port4C_GeometryFields, `Port4C_NativePrefix, `Port4C_PrefixMeaning, `Port4C_Reverse, `Port4C_OwnedInverse, `Port4C_InverseLoop, `Port4C_InverseBackend, `Port4C_BatchInverse, `Port4C_InverseExecution, `Port4C_OwnedGeometryInverse, `Port4C_GeometryInverse, `Port4C_FromFn, `Port4C_FromFnFixed, `Port4C_GeometryGroups, `Port4C_CollectStd, `Port4C_CollectLoop, `Port5Q1_GeometryTerminal, `Port5Q1_GeometryCanonical, `Port5Q1_Geometry, `Port5Q1_Domain, `Port5Q1_Gather, `Port5Q1_GeometryModel, `Port5Q1_ListCells, `Port5Q1_GeometryBinding, `Port5Q1_MapPoint, `Port5Q1_SelectedCells, `Port5Q1_GeometryLine, `Port5Q1_FlatPoint, `Port5Q1_WordShape, `Port5Q1_GeometryInverseCells, `Port5Q1_GeometryCells, `Port5Q1_GeometryReads, `Port5Q1_GeometryAccessor, `Port4C_RowStd, `Port4C_RowLoop, `Port4C_RowMeaning, `Port4C_BasisInner, `Port4C_BasisOuter, `Port4C_BasisMeaning, `Port4C_Accumulation, `Port4C_QueryMeaning, `Port4C_QueryLoop, `Port4C_SumField, `Port4C_FlushField, `Port4C_QueryState, `Port4C_FlushState, `Port5Q1_Advance, `Port5Q1_NodeModel, `Port5Q1_QueryPorts, `VTop_Erasure, `VTop_Run, `VTop_SecondFlow, `VTop_SecondOrder, `VTop_Order, `Port5Q1_Parsed, `Port5Q1_FoldedData, `Port5Q1_ObservedOpening, `Port5Q1_InstallPorts, `Port5Q1_FiveCells, `Port5Q1_DomainLanes, `Port5Q1_ObservedGeometry, `Port5Q1_LineModel, `Port5Q1_LineInputs ]
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

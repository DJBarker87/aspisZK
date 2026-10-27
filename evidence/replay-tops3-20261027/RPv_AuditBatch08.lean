import Lean
import RPv_FJh_ProjectedAfter
import RPv_FJa_PoseidonOrigins
import RPv_FJh_ProjectedCall
import RPv_FJh_GroupBounds
import RPv_FJh_GroupRange
import RPv_FJh_GroupSlices
import RPv_FJb_LimbMap
import RPv_RawPoseidonExternalRowLanes
import RPv_RawPoseidonExternalRowCalls
import RPv_RawPoseidonExternalAllRows
import RPv_FJb_RawRowCallbacks
import RPv_RawPoseidonExternalRowWrapperSlice
import RPv_RawPoseidonExternalRowWrapper
import RPv_RawPoseidonExternalRowExact
import RPv_FJb_RawRowValue
import RPv_FJb_LimbMeaning
import RPv_FJb_MatrixGroupStep
import RPv_FJb_WideSum4
import RPv_FJb_ColumnIndices
import RPv_FJb_ColumnCell
import RPv_FJb_MaskColumn
import RPv_FJb_ColumnRow
import RPv_FJb_ColumnTable
import RPv_FJb_TailCell
import RPv_FJb_RawValue
import RPv_FJb_TailRow
import RPv_FJb_ColumnBound
import RPv_FJb_TailStep
import RPv_FJb_WordAt
import RPv_FJb_ColumnWords
import RPv_FJb_GroupIndices
import RPv_FJb_MatrixBlock
import RPv_FJb_MatrixBlockLoop
import RPv_FJb_MatrixBlockValue
import RPv_FJb_MatrixModel
import RPv_FJb_ColumnMeaning
import RPv_FJb_MatrixLocality
import RPv_FJb_GroupedValues
import RPv_FJb_GroupedFold
import RPv_FJb_MatrixLoop
import RPv_FJb_TailLoop
import RPv_FJb_ExternalValue
import RPv_FJb_ExternalModel
import RPv_FJb_ExternalExact
import RPv_FJe_PackingLinear
import RPv_FJe_ExternalAdjoint
import RPv_FJh_SlicePackValue
import RPv_FJa_MapRelation
import RPv_FJh_MapCells
import RPv_FJa_PreparedMap
import RPv_FJh_PreparedCells
import RPv_FJh_ProjectedCallValue
import RPv_FJh_ProjectedArrayValue
import RPv_FJh_Fin16Indices
import RPv_FJh_ResidualModel
import RPv_FJh_Raw4Constructor
import RPv_FJh_InternalShiftsExact
import RPv_FJh_InternalWordOps
import RPv_FJh_InternalShiftCallEquation
import RPv_FJh_InternalClosureCallEquations
import RPv_FJh_InternalClosureSums
import RPv_FJh_InternalShiftClosure
import RPv_FJh_InternalRawArrays
import RPv_FJh_InternalAccumulateStep
import RPv_FJh_InternalAccumulateLimbs
import RPv_FJh_InternalStateWords
import RPv_FJh_InternalAccumulateState
import RPv_FJh_InternalAccumulatorModel
import RPv_FJh_RawLimbReassembly
import RPv_FJh_InternalLaneReassembly
import RPv_FJh_InternalLaneStep
import RPv_FJh_InternalLaneLoop
import RPv_FJh_InternalPrepare
import RPv_FJh_InternalLinearExact
import RPv_FJh_InternalRoundModel
import RPv_FJh_InternalRoundValue
import RPv_FJh_InternalPairOrigins
import RPv_FJh_M31DotSource
import RPv_FJh_M31DotOuterSource
import RPv_FJh_M31DotChunkIterator
import RPv_FJh_M31DotWordStep
import RPv_FJh_M31DotInput
import RPv_FJh_M31DotChunkSource
import RPv_FJh_M31DotReads
import RPv_FJh_M31DotChunkModel
import RPv_FJh_M31DotReduceStep
import RPv_FJh_M31DotReduceLoop
import RPv_FJh_M31DotOuterStep
import RPv_FJh_M31DotFieldSum
import RPv_FJh_M31DotRemainingAlgebra
import RPv_FJh_M31DotSevenOuter
import RPv_FJh_M31DotSevenExact
import RPv_FJh_InternalDotValue
import RPv_FJh_InternalWeights
import RPv_FJh_SmallIndices
import RPv_FJh_InternalConstantIndices
import RPv_FJh_InternalConstants
import RPv_FJh_InternalConstantCalls
import RPv_FJh_InternalPairValue
import RPv_FJe_PackedRawCallbacks
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJh_ProjectedAfter, `RPv_FJa_PoseidonOrigins, `RPv_FJh_ProjectedCall, `RPv_FJh_GroupBounds, `RPv_FJh_GroupRange, `RPv_FJh_GroupSlices, `RPv_FJb_LimbMap, `RPv_RawPoseidonExternalRowLanes, `RPv_RawPoseidonExternalRowCalls, `RPv_RawPoseidonExternalAllRows, `RPv_FJb_RawRowCallbacks, `RPv_RawPoseidonExternalRowWrapperSlice, `RPv_RawPoseidonExternalRowWrapper, `RPv_RawPoseidonExternalRowExact, `RPv_FJb_RawRowValue, `RPv_FJb_LimbMeaning, `RPv_FJb_MatrixGroupStep, `RPv_FJb_WideSum4, `RPv_FJb_ColumnIndices, `RPv_FJb_ColumnCell, `RPv_FJb_MaskColumn, `RPv_FJb_ColumnRow, `RPv_FJb_ColumnTable, `RPv_FJb_TailCell, `RPv_FJb_RawValue, `RPv_FJb_TailRow, `RPv_FJb_ColumnBound, `RPv_FJb_TailStep, `RPv_FJb_WordAt, `RPv_FJb_ColumnWords, `RPv_FJb_GroupIndices, `RPv_FJb_MatrixBlock, `RPv_FJb_MatrixBlockLoop, `RPv_FJb_MatrixBlockValue, `RPv_FJb_MatrixModel, `RPv_FJb_ColumnMeaning, `RPv_FJb_MatrixLocality, `RPv_FJb_GroupedValues, `RPv_FJb_GroupedFold, `RPv_FJb_MatrixLoop, `RPv_FJb_TailLoop, `RPv_FJb_ExternalValue, `RPv_FJb_ExternalModel, `RPv_FJb_ExternalExact, `RPv_FJe_PackingLinear, `RPv_FJe_ExternalAdjoint, `RPv_FJh_SlicePackValue, `RPv_FJa_MapRelation, `RPv_FJh_MapCells, `RPv_FJa_PreparedMap, `RPv_FJh_PreparedCells, `RPv_FJh_ProjectedCallValue, `RPv_FJh_ProjectedArrayValue, `RPv_FJh_Fin16Indices, `RPv_FJh_ResidualModel, `RPv_FJh_Raw4Constructor, `RPv_FJh_InternalShiftsExact, `RPv_FJh_InternalWordOps, `RPv_FJh_InternalShiftCallEquation, `RPv_FJh_InternalClosureCallEquations, `RPv_FJh_InternalClosureSums, `RPv_FJh_InternalShiftClosure, `RPv_FJh_InternalRawArrays, `RPv_FJh_InternalAccumulateStep, `RPv_FJh_InternalAccumulateLimbs, `RPv_FJh_InternalStateWords, `RPv_FJh_InternalAccumulateState, `RPv_FJh_InternalAccumulatorModel, `RPv_FJh_RawLimbReassembly, `RPv_FJh_InternalLaneReassembly, `RPv_FJh_InternalLaneStep, `RPv_FJh_InternalLaneLoop, `RPv_FJh_InternalPrepare, `RPv_FJh_InternalLinearExact, `RPv_FJh_InternalRoundModel, `RPv_FJh_InternalRoundValue, `RPv_FJh_InternalPairOrigins, `RPv_FJh_M31DotSource, `RPv_FJh_M31DotOuterSource, `RPv_FJh_M31DotChunkIterator, `RPv_FJh_M31DotWordStep, `RPv_FJh_M31DotInput, `RPv_FJh_M31DotChunkSource, `RPv_FJh_M31DotReads, `RPv_FJh_M31DotChunkModel, `RPv_FJh_M31DotReduceStep, `RPv_FJh_M31DotReduceLoop, `RPv_FJh_M31DotOuterStep, `RPv_FJh_M31DotFieldSum, `RPv_FJh_M31DotRemainingAlgebra, `RPv_FJh_M31DotSevenOuter, `RPv_FJh_M31DotSevenExact, `RPv_FJh_InternalDotValue, `RPv_FJh_InternalWeights, `RPv_FJh_SmallIndices, `RPv_FJh_InternalConstantIndices, `RPv_FJh_InternalConstants, `RPv_FJh_InternalConstantCalls, `RPv_FJh_InternalPairValue, `RPv_FJe_PackedRawCallbacks ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPV_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPV_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPV_AUDIT_COMPLETE declarations={count} modules={selected.size}"

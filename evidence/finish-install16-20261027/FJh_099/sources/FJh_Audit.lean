import FJe_Audit
import FJh_Base
import FJh_Fin16Indices
import FJh_GroupBounds
import FJh_GroupRange
import FJh_GroupSlices
import FJh_InternalAccumulateLimbs
import FJh_InternalAccumulateState
import FJh_InternalAccumulateStep
import FJh_InternalAccumulatorModel
import FJh_InternalClosureCallEquations
import FJh_InternalClosureSums
import FJh_InternalConstantCalls
import FJh_InternalConstantIndices
import FJh_InternalConstants
import FJh_InternalDotValue
import FJh_InternalLaneLoop
import FJh_InternalLaneReassembly
import FJh_InternalLaneStep
import FJh_InternalLinearExact
import FJh_InternalOnRun
import FJh_InternalPairOrigins
import FJh_InternalPairValue
import FJh_InternalPrepare
import FJh_InternalRawArrays
import FJh_InternalRoundModel
import FJh_InternalRoundValue
import FJh_InternalShiftCallEquation
import FJh_InternalShiftClosure
import FJh_InternalShiftsExact
import FJh_InternalStateWords
import FJh_InternalWeights
import FJh_InternalWordOps
import FJh_LinearNonvacuity
import FJh_LowModels
import FJh_M31DotChunkIterator
import FJh_M31DotChunkModel
import FJh_M31DotChunkSource
import FJh_M31DotFieldSum
import FJh_M31DotInput
import FJh_M31DotOuterSource
import FJh_M31DotOuterStep
import FJh_M31DotReads
import FJh_M31DotReduceLoop
import FJh_M31DotReduceStep
import FJh_M31DotRemainingAlgebra
import FJh_M31DotSevenExact
import FJh_M31DotSevenOuter
import FJh_M31DotSource
import FJh_M31DotWordStep
import FJh_MapCells
import FJh_Native07RawValue
import FJh_Native07RawWide
import FJh_PackResidual
import FJh_PoseidonOnComposition
import FJh_PreparedCells
import FJh_ProjectedAfter
import FJh_ProjectedArrayValue
import FJh_ProjectedCall
import FJh_ProjectedCallValue
import FJh_Raw4Constructor
import FJh_RawLimbReassembly
import FJh_ResidualModel
import FJh_ScalarInspect
import FJh_SlicePackValue
import FJh_SmallIndices
import FJh_WidePack
#print axioms AspisR1.FJh_Base.cell_set
#print axioms AspisR1.FJh_Base.set_canonical
#print axioms AspisR1.FJh_Base.set_overwrite
#print axioms AspisR1.FJh_Fin16Indices.zero
#print axioms AspisR1.FJh_Fin16Indices.one
#print axioms AspisR1.FJh_Fin16Indices.nine
#print axioms AspisR1.FJh_Fin16Indices.ten
#print axioms AspisR1.FJh_GroupBounds.value
#print axioms AspisR1.FJh_GroupRange.group_range_success
#print axioms AspisR1.FJh_GroupSlices.slice_length_four
#print axioms AspisR1.FJh_GroupSlices.source_slice_read
#print axioms AspisR1.FJh_GroupSlices.slice_input_eq
#print axioms AspisR1.FJh_InternalAccumulateLimbs.loop_success_fuel
#print axioms AspisR1.FJh_InternalAccumulateLimbs.source_success
#print axioms AspisR1.FJh_InternalAccumulateState.source_loop_eq
#print axioms AspisR1.FJh_InternalAccumulateState.loop_success_fuel
#print axioms AspisR1.FJh_InternalAccumulateState.zero_value
#print axioms AspisR1.FJh_InternalAccumulateState.source_success
#print axioms AspisR1.FJh_InternalAccumulateStep.step_success
#print axioms AspisR1.FJh_InternalAccumulateStep.source_step
#print axioms AspisR1.FJh_InternalAccumulatorModel.wordVec_decode
#print axioms AspisR1.FJh_InternalAccumulatorModel.wordNat_decode
#print axioms AspisR1.FJh_InternalAccumulatorModel.remaining_decode_eq_sum
#print axioms AspisR1.FJh_InternalAccumulatorModel.source_success
#print axioms AspisR1.FJh_InternalClosureCallEquations.full_call_eq
#print axioms AspisR1.FJh_InternalClosureCallEquations.zero_call_eq
#print axioms AspisR1.FJh_InternalClosureSums.full_sum_call
#print axioms AspisR1.FJh_InternalClosureSums.zero_sum_call
#print axioms AspisR1.FJh_InternalConstantCalls.even_call
#print axioms AspisR1.FJh_InternalConstantCalls.odd_call
#print axioms AspisR1.FJh_InternalConstantCalls.cells
#print axioms AspisR1.FJh_InternalConstantCalls.even_value
#print axioms AspisR1.FJh_InternalConstantCalls.odd_value
#print axioms AspisR1.FJh_InternalConstantIndices.value
#print axioms AspisR1.FJh_InternalConstants.read
#print axioms AspisR1.FJh_InternalConstants.canonical
#print axioms AspisR1.FJh_InternalConstants.model
#print axioms AspisR1.FJh_InternalDotValue.value
#print axioms AspisR1.FJh_InternalLaneLoop.loop_success_fuel
#print axioms AspisR1.FJh_InternalLaneLoop.source_success
#print axioms AspisR1.FJh_InternalLaneReassembly.zero_source
#print axioms AspisR1.FJh_InternalLaneReassembly.shift_source
#print axioms AspisR1.FJh_InternalLaneStep.source_loop_eq
#print axioms AspisR1.FJh_InternalLaneStep.step_success
#print axioms AspisR1.FJh_InternalLinearExact.source_success
#print axioms AspisR1.FJh_InternalOnRun.value
#print axioms AspisR1.FJh_InternalPairOrigins.reached
#print axioms AspisR1.FJh_InternalPairValue.value
#print axioms AspisR1.FJh_InternalPrepare.wrapper_factor
#print axioms AspisR1.FJh_InternalPrepare.source_success
#print axioms AspisR1.FJh_InternalRawArrays.full_source
#print axioms AspisR1.FJh_InternalRawArrays.zero_source
#print axioms AspisR1.FJh_InternalRawArrays.shift_source
#print axioms AspisR1.FJh_InternalRoundModel.update
#print axioms AspisR1.FJh_InternalRoundValue.value
#print axioms AspisR1.FJh_InternalShiftCallEquation.source_eq
#print axioms AspisR1.FJh_InternalShiftClosure.source_success
#print axioms AspisR1.FJh_InternalShiftsExact.source_read
#print axioms AspisR1.FJh_InternalShiftsExact.model
#print axioms AspisR1.FJh_InternalShiftsExact.bounded
#print axioms AspisR1.FJh_InternalStateWords.wordVec_source
#print axioms AspisR1.FJh_InternalStateWords.wordVec_canonical
#print axioms AspisR1.FJh_InternalStateWords.state_source_read
#print axioms AspisR1.FJh_InternalStateWords.wordNat_read
#print axioms AspisR1.FJh_InternalWeights.index_value
#print axioms AspisR1.FJh_InternalWeights.read
#print axioms AspisR1.FJh_InternalWeights.value
#print axioms AspisR1.FJh_InternalWordOps.wide_value
#print axioms AspisR1.FJh_InternalWordOps.shifted_word_success
#print axioms AspisR1.FJh_InternalWordOps.shiftedAdd_success
#print axioms AspisR1.FJh_InternalWordOps.sourceP_value
#print axioms AspisR1.FJh_InternalWordOps.zeroSubtract_success
#print axioms AspisR1.FJh_InternalWordOps.zeroSubtract_model
#print axioms AspisR1.FJh_LinearNonvacuity.value
#print axioms AspisR1.FJh_LowModels.cell
#print axioms AspisR1.FJh_LowModels.internal
#print axioms AspisR1.FJh_M31DotChunkIterator.initial_source
#print axioms AspisR1.FJh_M31DotChunkIterator.next_step
#print axioms AspisR1.FJh_M31DotChunkIterator.next_done
#print axioms AspisR1.FJh_M31DotChunkModel.loop_success_fuel
#print axioms AspisR1.FJh_M31DotChunkModel.source_success
#print axioms AspisR1.FJh_M31DotChunkSource.source_loop_eq
#print axioms AspisR1.FJh_M31DotFieldSum.decodeWords_list_coordinate_sum
#print axioms AspisR1.FJh_M31DotFieldSum.decodeWords_ofFn_coordinate_sum
#print axioms AspisR1.FJh_M31DotFieldSum.decode_wordVec_weighted
#print axioms AspisR1.FJh_M31DotFieldSum.decode_coordinatewise_nat_weighted_sum
#print axioms AspisR1.FJh_M31DotInput.source_success
#print axioms AspisR1.FJh_M31DotOuterSource.finish_source_eq
#print axioms AspisR1.FJh_M31DotOuterSource.source_loop_eq
#print axioms AspisR1.FJh_M31DotOuterSource.source_long_eq
#print axioms AspisR1.FJh_M31DotOuterStep.source_advance
#print axioms AspisR1.FJh_M31DotReads.source_read
#print axioms AspisR1.FJh_M31DotReads.term_read
#print axioms AspisR1.FJh_M31DotReduceLoop.source_loop_eq
#print axioms AspisR1.FJh_M31DotReduceLoop.loop_success_fuel
#print axioms AspisR1.FJh_M31DotReduceLoop.source_success
#print axioms AspisR1.FJh_M31DotReduceStep.source_success
#print axioms AspisR1.FJh_M31DotRemainingAlgebra.remaining_add
#print axioms AspisR1.FJh_M31DotRemainingAlgebra.remaining_ofFn
#print axioms AspisR1.FJh_M31DotRemainingAlgebra.decode_remaining
#print axioms AspisR1.FJh_M31DotSevenExact.source_success
#print axioms AspisR1.FJh_M31DotSevenOuter.len_seven
#print axioms AspisR1.FJh_M31DotSevenOuter.source_success
#print axioms AspisR1.FJh_M31DotWordStep.wide_value
#print axioms AspisR1.FJh_M31DotWordStep.four_products_fit
#print axioms AspisR1.FJh_M31DotWordStep.source_success
#print axioms AspisR1.FJh_MapCells.get
#print axioms AspisR1.FJh_Native07RawValue.value
#print axioms AspisR1.FJh_Native07RawWide.value
#print axioms AspisR1.FJh_PackResidual.value
#print axioms AspisR1.FJh_PoseidonOnComposition.value
#print axioms AspisR1.FJh_PreparedCells.value
#print axioms AspisR1.FJh_ProjectedAfter.value
#print axioms AspisR1.FJh_ProjectedArrayValue.value
#print axioms AspisR1.FJh_ProjectedCall.factor
#print axioms AspisR1.FJh_ProjectedCall.reached
#print axioms AspisR1.FJh_ProjectedCallValue.value
#print axioms AspisR1.FJh_Raw4Constructor.source_success
#print axioms AspisR1.FJh_RawLimbReassembly.source_success
#print axioms AspisR1.FJh_ResidualModel.value
#print axioms AspisR1.FJh_SlicePackValue.value
#print axioms AspisR1.FJh_SmallIndices.value
#print axioms AspisR1.FJh_WidePack.value
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.Rc10_Nonvacuity.composed
#print axioms AspisR1.FIr_Nonvacuity.composed

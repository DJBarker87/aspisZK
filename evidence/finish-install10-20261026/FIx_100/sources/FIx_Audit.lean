import FIx_Absorption
import FIx_AbsorptionArray
import FIx_ArithmeticTotal
import FIx_ArrayMeaning
import FIx_Builder
import FIx_ConservationMeaning
import FIx_HighSum
import FIx_HighSumInner
import FIx_HighSumOuter
import FIx_InitialArray
import FIx_InitialVariant
import FIx_InitialWrites
import FIx_PackingNonvacuity
import FIx_PathAlgebra
import FIx_PathIndices
import FIx_PathLiteral
import FIx_PathLoop
import FIx_PathLoopStep
import FIx_PathMeaning
import FIx_PathModel
import FIx_PathPacked
import FIx_PathStep
import FIx_Preweighted
import FIx_PreweightedGroup
import FIx_PreweightedLanes
import FIx_PreweightedLoop
import FIx_PreweightedLoopStep
import FIx_PreweightedMeaning
import FIx_PreweightedModel
import FIx_PreweightedPack
import FIx_PreweightedPointwise
import FIx_PreweightedSelect
import FIx_ReconstructFold
import FIx_ReconstructMeaning
import FIx_ReconstructPrefixModel
import FIx_ReconstructSlice
import FIx_ReconstructSliceValue
import FIx_ReconstructSource
import FIx_ReconstructStep
import FIx_ReconstructTraversal
import FIx_ReconstructValue
import FIx_ScheduleIndices
import FIx_ScheduleModel
import FIx_SchedulePacked
import FIx_ScheduleValue
import FIx_SelectedMeaning
import FIx_SquareMap
import FIx_SquareValue
import FIx_ValueBitClosed
import FIx_ValueBitModel
import FIx_ValueBitPrefix
import FIx_ValueBits0
import FIx_ValueBits1
import FIx_ValueBits2
import FIx_ValueConservation
import FIx_ValueConservationSource
import FIx_ValueIndices
import FIx_WordArithmetic
import FIw_Baseline
set_option autoImplicit false
#print AspisR1.Rc10_Top.deployed
#print AspisR1.FIr_Top.deployed
#print AspisR1.Rc10_Nonvacuity.composed
#print AspisR1.FIr_Nonvacuity.composed
#print AspisR1.FIx_SchedulePacked.value
#print AspisR1.FIx_PathPacked.value
#print AspisR1.FIx_ValueBitPrefix.value
#print AspisR1.FIx_ReconstructMeaning.value
#print AspisR1.FIx_ConservationMeaning.value
#print AspisR1.FIx_PackingNonvacuity.high_source
#print axioms AspisR1.FIx_Absorption.block_value
#print axioms AspisR1.FIx_Absorption.callback_value
#print axioms AspisR1.FIx_AbsorptionArray.value
#print axioms AspisR1.FIx_ArithmeticTotal.map_success
#print axioms AspisR1.FIx_ArithmeticTotal.add
#print axioms AspisR1.FIx_ArithmeticTotal.mul
#print axioms AspisR1.FIx_ArrayMeaning.decoded_of_map
#print axioms AspisR1.FIx_ArrayMeaning.decoded_repeat
#print axioms AspisR1.FIx_Builder.loop
#print axioms AspisR1.FIx_Builder.fromFn
#print axioms AspisR1.FIx_ConservationMeaning.index
#print axioms AspisR1.FIx_ConservationMeaning.value
#print axioms AspisR1.FIx_HighSum.source
#print axioms AspisR1.FIx_HighSum.value
#print axioms AspisR1.FIx_HighSumInner.read
#print axioms AspisR1.FIx_HighSumInner.value
#print axioms AspisR1.FIx_HighSumOuter.next_nil
#print axioms AspisR1.FIx_HighSumOuter.next_cons
#print axioms AspisR1.FIx_HighSumOuter.value
#print axioms AspisR1.FIx_InitialArray.callback_value
#print axioms AspisR1.FIx_InitialArray.value
#print axioms AspisR1.FIx_InitialVariant.value
#print axioms AspisR1.FIx_InitialWrites.rate_fin
#print axioms AspisR1.FIx_InitialWrites.nine_fin
#print axioms AspisR1.FIx_InitialWrites.rate_ne_nine
#print axioms AspisR1.FIx_InitialWrites.value
#print axioms AspisR1.FIx_PackingNonvacuity.high_source
#print axioms AspisR1.FIx_PathAlgebra.value
#print axioms AspisR1.FIx_PathIndices.first
#print axioms AspisR1.FIx_PathIndices.rate
#print axioms AspisR1.FIx_PathIndices.digest
#print axioms AspisR1.FIx_PathIndices.final
#print axioms AspisR1.FIx_PathIndices.source_bound
#print axioms AspisR1.FIx_PathIndices.rate_bound
#print axioms AspisR1.FIx_PathIndices.first_bound
#print axioms AspisR1.FIx_PathIndices.last_bound
#print axioms AspisR1.FIx_PathLiteral.value
#print axioms AspisR1.FIx_PathLoop.value
#print axioms AspisR1.FIx_PathLoopStep.value
#print axioms AspisR1.FIx_PathMeaning.value
#print axioms AspisR1.FIx_PathModel.value
#print axioms AspisR1.FIx_PathPacked.range_bounds
#print axioms AspisR1.FIx_PathPacked.value
#print axioms AspisR1.FIx_PathStep.value
#print axioms AspisR1.FIx_Preweighted.value
#print axioms AspisR1.FIx_PreweightedGroup.value
#print axioms AspisR1.FIx_PreweightedLanes.value
#print axioms AspisR1.FIx_PreweightedLoop.value
#print axioms AspisR1.FIx_PreweightedLoopStep.value
#print axioms AspisR1.FIx_PreweightedMeaning.value
#print axioms AspisR1.FIx_PreweightedModel.value
#print axioms AspisR1.FIx_PreweightedPack.value
#print axioms AspisR1.FIx_PreweightedPointwise.outside
#print axioms AspisR1.FIx_PreweightedPointwise.value
#print axioms AspisR1.FIx_PreweightedSelect.value
#print axioms AspisR1.FIx_ReconstructFold.value
#print axioms AspisR1.FIx_ReconstructMeaning.value
#print axioms AspisR1.FIx_ReconstructPrefixModel.take_step
#print axioms AspisR1.FIx_ReconstructPrefixModel.model_append
#print axioms AspisR1.FIx_ReconstructPrefixModel.value
#print axioms AspisR1.FIx_ReconstructSlice.value
#print axioms AspisR1.FIx_ReconstructSource.reached
#print axioms AspisR1.FIx_ReconstructStep.value
#print axioms AspisR1.FIx_ReconstructTraversal.nil
#print axioms AspisR1.FIx_ReconstructTraversal.append
#print axioms AspisR1.FIx_ReconstructValue.value
#print axioms AspisR1.FIx_ScheduleIndices.rate_bound
#print axioms AspisR1.FIx_ScheduleIndices.rate_plus_one
#print axioms AspisR1.FIx_ScheduleIndices.nine_bound
#print axioms AspisR1.FIx_ScheduleIndices.node_bounds
#print axioms AspisR1.FIx_SchedulePacked.value
#print axioms AspisR1.FIx_ScheduleValue.value
#print axioms AspisR1.FIx_SelectedMeaning.read
#print axioms AspisR1.FIx_SelectedMeaning.value
#print axioms AspisR1.FIx_SelectedMeaning.increment
#print axioms AspisR1.FIx_SquareMap.cm_double
#print axioms AspisR1.FIx_SquareMap.cm_square
#print axioms AspisR1.FIx_SquareMap.mapped
#print axioms AspisR1.FIx_SquareValue.value
#print axioms AspisR1.FIx_ValueBitClosed.value
#print axioms AspisR1.FIx_ValueBitPrefix.value
#print axioms AspisR1.FIx_ValueBits0.value
#print axioms AspisR1.FIx_ValueBits1.value
#print axioms AspisR1.FIx_ValueBits2.value
#print axioms AspisR1.FIx_ValueConservation.value
#print axioms AspisR1.FIx_ValueConservationSource.value
#print axioms AspisR1.FIx_ValueIndices.inc
#print axioms AspisR1.FIx_ValueIndices.offset
#print axioms AspisR1.FIx_ValueIndices.bound
#print axioms AspisR1.FIx_WordArithmetic.sub
#print axioms AspisR1.FIx_WordArithmetic.div
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.Rc10_Nonvacuity.composed
#print axioms AspisR1.FIr_Nonvacuity.composed

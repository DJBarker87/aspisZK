import FJb_ArrayTransport
import FJb_BuilderSelected
import FJb_BuilderStable
import FJb_BuilderTotal
import FJb_ColumnBound
import FJb_ColumnCell
import FJb_ColumnIndices
import FJb_ColumnMeaning
import FJb_ColumnRow
import FJb_ColumnTable
import FJb_ColumnWords
import FJb_ExternalExact
import FJb_ExternalModel
import FJb_ExternalValue
import FJb_GroupIndices
import FJb_GroupedFold
import FJb_GroupedValues
import FJb_InitialConstants
import FJb_LeadingLoop
import FJb_LeadingOnRun
import FJb_LeadingStep
import FJb_LimbMap
import FJb_LimbMeaning
import FJb_M31LazyRound
import FJb_M31Loop
import FJb_M31LoopStep
import FJb_M31Scalar
import FJb_M31Step
import FJb_MaskColumn
import FJb_MatrixBlock
import FJb_MatrixBlockLoop
import FJb_MatrixBlockValue
import FJb_MatrixGroupStep
import FJb_MatrixLocality
import FJb_MatrixLoop
import FJb_MatrixModel
import FJb_PairBind
import FJb_PairProjection
import FJb_Prerequisites
import FJb_QmLazyRound
import FJb_QmRoundLoop
import FJb_QmRoundStep
import FJb_RawConversion
import FJb_RawRowCallbacks
import FJb_RawRowValue
import FJb_RawValue
import FJb_TailCell
import FJb_TailLoop
import FJb_TailRow
import FJb_TailStep
import FJb_WideSum4
import FJb_WordAt
import Rc10_Top
import FIr_Top
import Rc10_Nonvacuity
import FIr_Nonvacuity

#print AspisR1.Rc10_Top.deployed
#print AspisR1.FIr_Top.deployed
#print AspisR1.Rc10_Nonvacuity.composed
#print AspisR1.FIr_Nonvacuity.composed

#print axioms AspisR1.FJb_ArrayTransport.index
#print axioms AspisR1.FJb_ArrayTransport.update
#print axioms AspisR1.FJb_BuilderSelected.value
#print axioms AspisR1.FJb_BuilderStable.transport
#print axioms AspisR1.FJb_BuilderStable.total
#print axioms AspisR1.FJb_BuilderTotal.loop
#print axioms AspisR1.FJb_BuilderTotal.value
#print axioms AspisR1.FJb_ColumnBound.value
#print axioms AspisR1.FJb_ColumnCell.value
#print axioms AspisR1.FJb_ColumnIndices.value
#print axioms AspisR1.FJb_ColumnMeaning.q_value
#print axioms AspisR1.FJb_ColumnMeaning.value
#print axioms AspisR1.FJb_ColumnMeaning.meaning
#print axioms AspisR1.FJb_ColumnRow.total
#print axioms AspisR1.FJb_ColumnRow.value
#print axioms AspisR1.FJb_ColumnTable.callback_total
#print axioms AspisR1.FJb_ColumnTable.value
#print axioms AspisR1.FJb_ColumnWords.value
#print axioms AspisR1.FJb_ExternalExact.value
#print axioms AspisR1.FJb_ExternalModel.sample_group
#print axioms AspisR1.FJb_ExternalModel.at_index
#print axioms AspisR1.FJb_ExternalModel.value
#print axioms AspisR1.FJb_ExternalValue.value
#print axioms AspisR1.FJb_GroupIndices.value
#print axioms AspisR1.FJb_GroupedFold.value
#print axioms AspisR1.FJb_GroupedFold.full
#print axioms AspisR1.FJb_GroupedValues.inside
#print axioms AspisR1.FJb_GroupedValues.preserved
#print axioms AspisR1.FJb_InitialConstants.read
#print axioms AspisR1.FJb_InitialConstants.bounded
#print axioms AspisR1.FJb_InitialConstants.model
#print axioms AspisR1.FJb_LeadingLoop.value
#print axioms AspisR1.FJb_LeadingOnRun.value
#print axioms AspisR1.FJb_LeadingStep.value
#print axioms AspisR1.FJb_LeadingStep.unfold_loop
#print axioms AspisR1.FJb_LimbMap.value
#print axioms AspisR1.FJb_LimbMeaning.words
#print axioms AspisR1.FJb_LimbMeaning.value
#print axioms AspisR1.FJb_M31LazyRound.value
#print axioms AspisR1.FJb_M31Loop.value
#print axioms AspisR1.FJb_M31LoopStep.unfold_loop
#print axioms AspisR1.FJb_M31Scalar.value
#print axioms AspisR1.FJb_M31Step.value
#print axioms AspisR1.FJb_MaskColumn.value
#print axioms AspisR1.FJb_MaskColumn.bound
#print axioms AspisR1.FJb_MatrixBlock.factor
#print axioms AspisR1.FJb_MatrixBlock.unfold_loop
#print axioms AspisR1.FJb_MatrixBlock.value
#print axioms AspisR1.FJb_MatrixGroupStep.value
#print axioms AspisR1.FJb_MatrixLocality.outside
#print axioms AspisR1.FJb_MatrixLocality.sample_other
#print axioms AspisR1.FJb_MatrixLocality.sample_same
#print axioms AspisR1.FJb_MatrixLoop.value
#print axioms AspisR1.FJb_MatrixModel.at_value
#print axioms AspisR1.FJb_MatrixModel.model
#print axioms AspisR1.FJb_PairBind.value
#print axioms AspisR1.FJb_PairProjection.value
#print axioms AspisR1.FJb_QmLazyRound.value
#print axioms AspisR1.FJb_QmRoundLoop.value
#print axioms AspisR1.FJb_QmRoundStep.value
#print axioms AspisR1.FJb_QmRoundStep.unfold_loop
#print axioms AspisR1.FJb_RawConversion.reduce
#print axioms AspisR1.FJb_RawConversion.limbs
#print axioms AspisR1.FJb_RawConversion.converted
#print axioms AspisR1.FJb_RawRowCallbacks.same
#print axioms AspisR1.FJb_RawRowCallbacks.total
#print axioms AspisR1.FJb_RawRowValue.value
#print axioms AspisR1.FJb_RawValue.value
#print axioms AspisR1.FJb_TailCell.value
#print axioms AspisR1.FJb_TailLoop.value
#print axioms AspisR1.FJb_TailRow.value
#print axioms AspisR1.FJb_TailStep.column_eq
#print axioms AspisR1.FJb_TailStep.value
#print axioms AspisR1.FJb_TailStep.unfold_loop
#print axioms AspisR1.FJb_WideSum4.wide_val
#print axioms AspisR1.FJb_WideSum4.value
#print axioms AspisR1.FJb_WordAt.value
#print axioms AspisR1.FJb_WordAt.group
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.Rc10_Nonvacuity.composed
#print axioms AspisR1.FIr_Nonvacuity.composed

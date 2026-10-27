import FIz_Audit
import FJa_ArrayUpdate
import FJa_BoxedCanonical
import FJa_BoxedLiteral
import FJa_BoxedMass
import FJa_BoxedSelAt
import FJa_ClaimsCanonical
import FJa_ClaimsDecode
import FJa_ClaimsOnRun
import FJa_ClaimsReference
import FJa_ClaimsRows
import FJa_CoefficientsOnRun
import FJa_ExpandCanonical
import FJa_ExpandModel
import FJa_ExpandValue
import FJa_Expansion
import FJa_ExpansionMass
import FJa_ExpansionMeaning
import FJa_FoldPoint
import FJa_FoldShape
import FJa_FullLowWeight
import FJa_InclusiveFoldStep
import FJa_InclusiveNext
import FJa_InclusiveShape
import FJa_InclusiveSteps
import FJa_InternalLowShape
import FJa_InternalLowWeight
import FJa_LiteralNonvacuity
import FJa_LocalWeightFold
import FJa_LocalWeightStep
import FJa_MapRelation
import FJa_NativePoint
import FJa_PoseidonLowOnRun
import FJa_PoseidonOrigins
import FJa_PoseidonPow5
import FJa_PoseidonSelectors
import FJa_PoseidonShape
import FJa_PreparedMap
import FJa_PublicBounds
import FJa_PublicCopy
import FJa_PublicOnPreparation
import FJa_ReadersOnRun
import FJa_ReverseStep
import FJa_Seed
import FJa_SelectorOnRun
import FJa_SemanticPoint
import FJa_SliceBounds
import FJa_SliceShape
import FJa_SlicesValue
import FJa_SplitCanonical
import FJa_SplitFold
import FJa_SplitMass
import FJa_SplitModel
import FJa_SplitShape
import FJa_SplitStep
import FJa_SplitValue
import FJa_SquareMap
import FJa_SquareValue
import FJa_Statements
import FJa_TensorAtPoint
import FJa_TensorMeaning
import FJa_WeightAppend
import FJa_WeightBits
import FJa_WeightPeriod
#print axioms AspisR1.FJa_ArrayUpdate.bound
#print axioms AspisR1.FJa_ArrayUpdate.canonical_write
#print axioms AspisR1.FJa_ArrayUpdate.value
#print axioms AspisR1.FJa_BoxedCanonical.value
#print axioms AspisR1.FJa_BoxedLiteral.value
#print axioms AspisR1.FJa_BoxedMass.value
#print axioms AspisR1.FJa_BoxedSelAt.value
#print axioms AspisR1.FJa_ClaimsCanonical.value
#print axioms AspisR1.FJa_ClaimsDecode.value
#print axioms AspisR1.FJa_ClaimsOnRun.value
#print axioms AspisR1.FJa_ClaimsReference.reached
#print axioms AspisR1.FJa_ClaimsRows.value
#print axioms AspisR1.FJa_CoefficientsOnRun.value
#print axioms AspisR1.FJa_ExpandCanonical.loop
#print axioms AspisR1.FJa_ExpandModel.mass
#print axioms AspisR1.FJa_ExpandValue.loop
#print axioms AspisR1.FJa_Expansion.canonical_result
#print axioms AspisR1.FJa_ExpansionMass.value
#print axioms AspisR1.FJa_ExpansionMeaning.value
#print axioms AspisR1.FJa_FoldPoint.value
#print axioms AspisR1.FJa_FoldShape.outside
#print axioms AspisR1.FJa_FoldShape.children
#print axioms AspisR1.FJa_FullLowWeight.value
#print axioms AspisR1.FJa_InclusiveFoldStep.step
#print axioms AspisR1.FJa_InclusiveFoldStep.stop
#print axioms AspisR1.FJa_InclusiveNext.stop
#print axioms AspisR1.FJa_InclusiveNext.last
#print axioms AspisR1.FJa_InclusiveSteps.step2
#print axioms AspisR1.FJa_InclusiveSteps.step3
#print axioms AspisR1.FJa_InclusiveSteps.step4
#print axioms AspisR1.FJa_InclusiveSteps.step5
#print axioms AspisR1.FJa_InclusiveSteps.step6
#print axioms AspisR1.FJa_InclusiveSteps.step7
#print axioms AspisR1.FJa_InternalLowShape.value
#print axioms AspisR1.FJa_InternalLowWeight.value
#print axioms AspisR1.FJa_LiteralNonvacuity.mass
#print axioms AspisR1.FJa_LiteralNonvacuity.nonzero
#print axioms AspisR1.FJa_LocalWeightFold.value
#print axioms AspisR1.FJa_LocalWeightStep.value
#print axioms AspisR1.FJa_LocalWeightStep.internal
#print axioms AspisR1.FJa_MapRelation.loop
#print axioms AspisR1.FJa_MapRelation.value
#print axioms AspisR1.FJa_NativePoint.verified
#print axioms AspisR1.FJa_PoseidonLowOnRun.value
#print axioms AspisR1.FJa_PoseidonOrigins.reached
#print axioms AspisR1.FJa_PoseidonPow5.value
#print axioms AspisR1.FJa_PoseidonSelectors.value
#print axioms AspisR1.FJa_PreparedMap.value
#print axioms AspisR1.FJa_PublicBounds.digest_raw
#print axioms AspisR1.FJa_PublicBounds.frontier_raw
#print axioms AspisR1.FJa_PublicBounds.from_raw
#print axioms AspisR1.FJa_PublicCopy.on_statement
#print axioms AspisR1.FJa_PublicOnPreparation.value
#print axioms AspisR1.FJa_ReadersOnRun.value
#print axioms AspisR1.FJa_ReverseStep.stop
#print axioms AspisR1.FJa_ReverseStep.step
#print axioms AspisR1.FJa_Seed.value
#print axioms AspisR1.FJa_SelectorOnRun.value
#print axioms AspisR1.FJa_SemanticPoint.value
#print axioms AspisR1.FJa_SliceBounds.high
#print axioms AspisR1.FJa_SliceBounds.low
#print axioms AspisR1.FJa_SlicesValue.high
#print axioms AspisR1.FJa_SlicesValue.low
#print axioms AspisR1.FJa_SplitCanonical.value
#print axioms AspisR1.FJa_SplitFold.value
#print axioms AspisR1.FJa_SplitMass.pairs
#print axioms AspisR1.FJa_SplitMass.value
#print axioms AspisR1.FJa_SplitModel.lower
#print axioms AspisR1.FJa_SplitModel.left
#print axioms AspisR1.FJa_SplitModel.right
#print axioms AspisR1.FJa_SplitModel.outside
#print axioms AspisR1.FJa_SplitStep.value
#print axioms AspisR1.FJa_SplitValue.writes
#print axioms AspisR1.FJa_SquareMap.cm_square
#print axioms AspisR1.FJa_SquareMap.cm_double
#print axioms AspisR1.FJa_SquareMap.qm_square
#print axioms AspisR1.FJa_SquareValue.value
#print axioms AspisR1.FJa_TensorAtPoint.ofFn
#print axioms AspisR1.FJa_TensorAtPoint.list
#print axioms AspisR1.FJa_TensorMeaning.value
#print axioms AspisR1.FJa_WeightAppend.value
#print axioms AspisR1.FJa_WeightBits.value
#print axioms AspisR1.FJa_WeightPeriod.add
#print axioms AspisR1.FJa_WeightPeriod.mod
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.Rc10_Nonvacuity.composed
#print axioms AspisR1.FIr_Nonvacuity.composed

import Lean
import RPv_FJe_PackedRawRowValue
import RPv_FJe_PackedRawRow
import RPv_FJe_PackedRawTable
import RPv_PoseidonExternalPackedAlgebra
import RPv_FJe_RawReference
import RPv_FJe_Component0
import RPv_FJe_Component1
import RPv_FJe_Component2
import RPv_FJe_Component3
import RPv_FJe_PackedTableRead
import RPv_FJe_PackedRawAfter
import RPv_FJe_PackedBound
import RPv_FJe_PackedRawOrigins
import RPv_FJe_PackedInputWords
import RPv_FJe_PackedRawAfterValue
import RPv_FJe_PackedRawValue
import RPv_FJe_LocalPackedValue
import RPv_FJe_PackedGroupStep
import RPv_FJe_PackedLoopValue
import RPv_FJe_PackedLoopCanonical
import RPv_FJe_ExternalCalls
import RPv_FJe_ExternalSum
import RPv_FJe_ExternalMap
import RPv_FJe_PackedGroupModel
import RPv_FJe_ExternalPackedValue
import RPv_FJb_LeadingStep
import RPv_FJb_LeadingLoop
import RPv_FJb_LeadingOnRun
import RPv_FJb_M31Scalar
import RPv_FJb_M31Step
import RPv_FJb_InitialConstants
import RPv_FJb_PairBind
import RPv_FJb_M31LoopStep
import RPv_FJb_M31Loop
import RPv_FJb_M31LazyRound
import RPv_FJe_LeadingPrefix
import RPv_FJe_M31PackedNonlinear
import RPv_FJe_LeadingNonlinear
import RPv_FJe_LeadingPackedValue
import RPv_FJe_FinalConstants
import RPv_FJe_ThreeLimb
import RPv_FJe_ThreeLimbTotal
import RPv_FJe_ThreeCell
import RPv_FJe_ThreeColumnStep
import RPv_FJe_ThreeColumnLoop
import RPv_FJe_ThreeColumns
import RPv_FJe_FullCalls
import RPv_FJe_FullWeights
import RPv_FJe_FullConstants
import RPv_FJb_QmRoundStep
import RPv_FJb_QmRoundLoop
import RPv_FJb_QmLazyRound
import RPv_FJe_QmPackedNonlinear
import RPv_FJe_FullNonlinear
import RPv_FJe_FullPackedValue
import RPv_FJe_PackedValues
import RPv_FJa_LocalWeightStep
import RPv_FJa_LocalWeightFold
import RPv_FJa_FullLowWeight
import RPv_FJa_PoseidonShape
import RPv_FJa_InclusiveShape
import RPv_FJa_InclusiveNext
import RPv_FJa_InclusiveSteps
import RPv_FJa_InclusiveFoldStep
import RPv_FJa_InternalLowShape
import RPv_FJa_InternalLowWeight
import RPv_FJa_PoseidonLowOnRun
import RPv_FJh_LowModels
import RPv_FJh_PackResidual
import RPv_FJh_Native07RawValue
import RPv_FJk_ResidualLane
import RPv_FJk_ResidualPack
import RPv_FJh_WidePack
import RPv_FJh_Native07RawWide
import RPv_FJa_ArrayUpdate
import RPv_FJa_SplitStep
import RPv_FJa_SplitCanonical
import RPv_FJa_ExpandCanonical
import RPv_FJa_Expansion
import RPv_FJa_SliceShape
import RPv_FJa_SliceBounds
import RPv_FIr_AlphaCanonical
import RPv_FJa_NativePoint
import RPv_FJa_BoxedCanonical
import RPv_FJa_ClaimsDecode
import RPv_FJa_ClaimsRows
import RPv_FJa_ClaimsReference
import RPv_FJa_ClaimsCanonical
import RPv_FJa_ClaimsOnRun
import RPv_FJa_ReadersOnRun
import RPv_FJa_SplitModel
import RPv_FJa_SplitValue
import RPv_FJa_SplitFold
import RPv_FJa_FoldShape
import RPv_FJa_SplitMass
import RPv_FJa_ExpandModel
import RPv_FJa_ExpandValue
import RPv_FJa_FoldPoint
import RPv_FJa_TensorMeaning
import RPv_FJa_Seed
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJe_PackedRawRowValue, `RPv_FJe_PackedRawRow, `RPv_FJe_PackedRawTable, `RPv_PoseidonExternalPackedAlgebra, `RPv_FJe_RawReference, `RPv_FJe_Component0, `RPv_FJe_Component1, `RPv_FJe_Component2, `RPv_FJe_Component3, `RPv_FJe_PackedTableRead, `RPv_FJe_PackedRawAfter, `RPv_FJe_PackedBound, `RPv_FJe_PackedRawOrigins, `RPv_FJe_PackedInputWords, `RPv_FJe_PackedRawAfterValue, `RPv_FJe_PackedRawValue, `RPv_FJe_LocalPackedValue, `RPv_FJe_PackedGroupStep, `RPv_FJe_PackedLoopValue, `RPv_FJe_PackedLoopCanonical, `RPv_FJe_ExternalCalls, `RPv_FJe_ExternalSum, `RPv_FJe_ExternalMap, `RPv_FJe_PackedGroupModel, `RPv_FJe_ExternalPackedValue, `RPv_FJb_LeadingStep, `RPv_FJb_LeadingLoop, `RPv_FJb_LeadingOnRun, `RPv_FJb_M31Scalar, `RPv_FJb_M31Step, `RPv_FJb_InitialConstants, `RPv_FJb_PairBind, `RPv_FJb_M31LoopStep, `RPv_FJb_M31Loop, `RPv_FJb_M31LazyRound, `RPv_FJe_LeadingPrefix, `RPv_FJe_M31PackedNonlinear, `RPv_FJe_LeadingNonlinear, `RPv_FJe_LeadingPackedValue, `RPv_FJe_FinalConstants, `RPv_FJe_ThreeLimb, `RPv_FJe_ThreeLimbTotal, `RPv_FJe_ThreeCell, `RPv_FJe_ThreeColumnStep, `RPv_FJe_ThreeColumnLoop, `RPv_FJe_ThreeColumns, `RPv_FJe_FullCalls, `RPv_FJe_FullWeights, `RPv_FJe_FullConstants, `RPv_FJb_QmRoundStep, `RPv_FJb_QmRoundLoop, `RPv_FJb_QmLazyRound, `RPv_FJe_QmPackedNonlinear, `RPv_FJe_FullNonlinear, `RPv_FJe_FullPackedValue, `RPv_FJe_PackedValues, `RPv_FJa_LocalWeightStep, `RPv_FJa_LocalWeightFold, `RPv_FJa_FullLowWeight, `RPv_FJa_PoseidonShape, `RPv_FJa_InclusiveShape, `RPv_FJa_InclusiveNext, `RPv_FJa_InclusiveSteps, `RPv_FJa_InclusiveFoldStep, `RPv_FJa_InternalLowShape, `RPv_FJa_InternalLowWeight, `RPv_FJa_PoseidonLowOnRun, `RPv_FJh_LowModels, `RPv_FJh_PackResidual, `RPv_FJh_Native07RawValue, `RPv_FJk_ResidualLane, `RPv_FJk_ResidualPack, `RPv_FJh_WidePack, `RPv_FJh_Native07RawWide, `RPv_FJa_ArrayUpdate, `RPv_FJa_SplitStep, `RPv_FJa_SplitCanonical, `RPv_FJa_ExpandCanonical, `RPv_FJa_Expansion, `RPv_FJa_SliceShape, `RPv_FJa_SliceBounds, `RPv_FIr_AlphaCanonical, `RPv_FJa_NativePoint, `RPv_FJa_BoxedCanonical, `RPv_FJa_ClaimsDecode, `RPv_FJa_ClaimsRows, `RPv_FJa_ClaimsReference, `RPv_FJa_ClaimsCanonical, `RPv_FJa_ClaimsOnRun, `RPv_FJa_ReadersOnRun, `RPv_FJa_SplitModel, `RPv_FJa_SplitValue, `RPv_FJa_SplitFold, `RPv_FJa_FoldShape, `RPv_FJa_SplitMass, `RPv_FJa_ExpandModel, `RPv_FJa_ExpandValue, `RPv_FJa_FoldPoint, `RPv_FJa_TensorMeaning, `RPv_FJa_Seed ]
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

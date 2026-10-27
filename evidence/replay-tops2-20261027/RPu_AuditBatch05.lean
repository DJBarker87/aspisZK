import Lean
import RPu_FJc_ZeroArray
import RPu_FJc_InactiveCoefficientsValue
import RPu_FJc_SubsetStep
import RPu_FJc_SubsetValue
import RPu_FJc_InactiveContract
import RPu_FJc_InactiveContractValue
import RPu_FJc_InactiveValue
import RPu_FJc_PermTable
import RPu_FIo_ArrayBack
import RPu_FIp_ArraySetValue
import RPu_FIo_PowersCanonical
import RPu_FIp_PowersState
import RPu_FIp_PowersWrite
import RPu_FIp_PowersStep
import RPu_FIp_PowersValue
import RPu_FJc_LowPowers
import RPu_FJc_SliceCanonical
import RPu_FGm_RangeDone
import RPu_FGm_RangeStopBound
import RPu_FGm_ArrayValue
import RPu_FGm_Indices
import RPu_FGm_SubsetSelection
import RPu_FGm_SubsetStep
import RPu_FGm_SubsetValue
import RPu_FGm_ContractStep
import RPu_FGm_ContractValue
import RPu_FGm_GroupValue
import RPu_FGm_GroupDispatch
import RPu_FJc_InactiveFinalValue
import RPu_FJc_InstalledFinalPart0
import RPu_FJd_LoopReference
import RPu_FJr_DoubleValue
import RPu_FJr_CircleInnerCell
import RPu_FJr_CircleInnerWrite
import RPu_FJr_CircleInnerLoop
import RPu_FJr_CircleOuterCell
import RPu_R1SelectedCircleWeights
import RPu_FJr_CircleLiteral
import RPu_FJr_PairRows
import RPu_FJs_PointTransport
import RPu_FJs_CircleTransport
import RPu_FJs_LiteralRows
import RPu_FJf_RawPointFrame
import RPu_FJf_RawPointOuterFrame
import RPu_FJf_PointFirstCanon
import RPu_FJf_RawCircleFrame
import RPu_FJf_RawCircleOuterFrame
import RPu_FJf_OriginalCanon
import RPu_FJf_MapRead
import RPu_FJf_NativeFactors
import RPu_FJf_InstalledPointCell
import RPu_FJf_QMArray
import RPu_FJf_CommonIndices
import RPu_FJf_CommonCell
import RPu_FJf_CommonDone
import RPu_FJf_CommonStep
import RPu_FJf_CommonValue
import RPu_FJf_PartialCell
import RPu_FJf_PartialStep
import RPu_FJf_PartialValue
import RPu_FJf_PartialInstalled
import RPu_FJg_PairProvenance
import RPu_FJg_Part1Trace
import RPu_FJj_RegularTrace
import RPu_FJj_PairTrace
import RPu_FJj_SliceDivision
import RPu_FJm_LibraPairTrace
import RPu_FJj_RegularFrame
import RPu_FJg_SharedHighCall
import RPu_FJg_SharedHighTrace
import RPu_FJm_RawFrames
import RPu_FJm_LibraInitialSlot
import RPu_FJg_InstalledProvenance
import RPu_FJg_DigitProvenance
import RPu_FJg_DigitLoop
import RPu_FJg_PointProvenance
import RPu_FJg_SharedPoints
import RPu_FJg_DigitEqual
import RPu_FJg_ConstructorShared
import RPu_FJg_NativeShared
import RPu_FJg_GuardEquality
import RPu_FJg_SharedGuard
import RPu_FJg_SharedProvenance
import RPu_FJr_PairTrace
import RPu_FJc_GroupAlgebra
import RPu_FJr_InactiveRegroup
import RPu_FJr_Fin16Split
import RPu_FJg_Permutation
import RPu_FJr_DualFold16
import RPu_FIo_CanonicalQM
import RPu_FIo_MixedValues
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPu_FJc_ZeroArray, `RPu_FJc_InactiveCoefficientsValue, `RPu_FJc_SubsetStep, `RPu_FJc_SubsetValue, `RPu_FJc_InactiveContract, `RPu_FJc_InactiveContractValue, `RPu_FJc_InactiveValue, `RPu_FJc_PermTable, `RPu_FIo_ArrayBack, `RPu_FIp_ArraySetValue, `RPu_FIo_PowersCanonical, `RPu_FIp_PowersState, `RPu_FIp_PowersWrite, `RPu_FIp_PowersStep, `RPu_FIp_PowersValue, `RPu_FJc_LowPowers, `RPu_FJc_SliceCanonical, `RPu_FGm_RangeDone, `RPu_FGm_RangeStopBound, `RPu_FGm_ArrayValue, `RPu_FGm_Indices, `RPu_FGm_SubsetSelection, `RPu_FGm_SubsetStep, `RPu_FGm_SubsetValue, `RPu_FGm_ContractStep, `RPu_FGm_ContractValue, `RPu_FGm_GroupValue, `RPu_FGm_GroupDispatch, `RPu_FJc_InactiveFinalValue, `RPu_FJc_InstalledFinalPart0, `RPu_FJd_LoopReference, `RPu_FJr_DoubleValue, `RPu_FJr_CircleInnerCell, `RPu_FJr_CircleInnerWrite, `RPu_FJr_CircleInnerLoop, `RPu_FJr_CircleOuterCell, `RPu_R1SelectedCircleWeights, `RPu_FJr_CircleLiteral, `RPu_FJr_PairRows, `RPu_FJs_PointTransport, `RPu_FJs_CircleTransport, `RPu_FJs_LiteralRows, `RPu_FJf_RawPointFrame, `RPu_FJf_RawPointOuterFrame, `RPu_FJf_PointFirstCanon, `RPu_FJf_RawCircleFrame, `RPu_FJf_RawCircleOuterFrame, `RPu_FJf_OriginalCanon, `RPu_FJf_MapRead, `RPu_FJf_NativeFactors, `RPu_FJf_InstalledPointCell, `RPu_FJf_QMArray, `RPu_FJf_CommonIndices, `RPu_FJf_CommonCell, `RPu_FJf_CommonDone, `RPu_FJf_CommonStep, `RPu_FJf_CommonValue, `RPu_FJf_PartialCell, `RPu_FJf_PartialStep, `RPu_FJf_PartialValue, `RPu_FJf_PartialInstalled, `RPu_FJg_PairProvenance, `RPu_FJg_Part1Trace, `RPu_FJj_RegularTrace, `RPu_FJj_PairTrace, `RPu_FJj_SliceDivision, `RPu_FJm_LibraPairTrace, `RPu_FJj_RegularFrame, `RPu_FJg_SharedHighCall, `RPu_FJg_SharedHighTrace, `RPu_FJm_RawFrames, `RPu_FJm_LibraInitialSlot, `RPu_FJg_InstalledProvenance, `RPu_FJg_DigitProvenance, `RPu_FJg_DigitLoop, `RPu_FJg_PointProvenance, `RPu_FJg_SharedPoints, `RPu_FJg_DigitEqual, `RPu_FJg_ConstructorShared, `RPu_FJg_NativeShared, `RPu_FJg_GuardEquality, `RPu_FJg_SharedGuard, `RPu_FJg_SharedProvenance, `RPu_FJr_PairTrace, `RPu_FJc_GroupAlgebra, `RPu_FJr_InactiveRegroup, `RPu_FJr_Fin16Split, `RPu_FJg_Permutation, `RPu_FJr_DualFold16, `RPu_FIo_CanonicalQM, `RPu_FIo_MixedValues ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPU_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPU_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPU_AUDIT_COMPLETE declarations={count} modules={selected.size}"

import Lean
import RPt_JFq_Sem07
import RPt_JFq_Sem08
import RPt_JFq_Sem09
import RPt_JFq_Semantic
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
import RPt_JFq_Claim
import RPt_JFq_Rhs
import RPt_JFq_Power
import RPt_JFq_Weights00
import RPt_JFq_Weights01
import RPt_JFq_Weights02
import RPt_JFq_Weights03
import RPt_JFq_Weights04
import RPt_JFq_Weights05
import RPt_JFq_Weights06
import RPt_JFq_Weights07
import RPt_JFq_Weights08
import RPt_JFq_Weights09
import RPt_JFq_Weights10
import RPt_JFq_Weights11
import RPt_JFq_Weights12
import RPt_JFq_Weights13
import RPt_JFq_Weights14
import RPt_JFq_Weights15
import RPt_JFq_ReadSequence
import RPt_JFq_WeightReads
import RPt_JFo_WeightRestore
import RPt_JFo_Weights
import RPt_JFo_Prepared
import RPt_JFo_Opening
import RPt_JFo_QueryRead
import RPt_JFn_FieldRead
import RPt_JFn_ValueBlock
import RPt_JFo_PrefixRead
import RPt_JFr_TX2_Windows
import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DotStep
import RPt_JFr_TX2_DotLanes
import RPt_JFr_TX2_DotBounds
import RPt_JFr_TX2_DotLaneTotal
import RPt_FJi_LaneValue
import RPt_FJi_Coordinate0
import RPt_FJi_Coordinate1
import RPt_FJi_Coordinate2
import RPt_FJi_Coordinate3
import RPt_FJi_Coordinate4
import RPt_FJi_Coordinate5
import RPt_FJi_Coordinate6
import RPt_FJi_Coordinate7
import RPt_FJi_EightValue
import RPt_FJi_Inputs
import RPt_FJi_TermValue
import RPt_FJi_InnerStep
import RPt_FJi_InnerValue
import RPt_JFs_TX2_Eight
import RPt_JFs_TX2_ArrayEight
import RPt_JFv_TX2_ArrayMeaning
import RPt_JFs_TX2_FoldLane
import RPt_JFs_TX2_FoldEight
import RPt_JFv_TX2_FoldMeaning
import RPt_JFv_TX2_FoldValue
import RPt_JFr_TX2_DecodeCell
import RPt_JFr_TX2_Slot10_0
import RPt_JFr_TX2_Slot10_1
import RPt_JFr_TX2_Slot10_2
import RPt_JFr_TX2_Slot10_3
import RPt_JFr_TX2_Slot11_0
import RPt_JFr_TX2_Slot11_1
import RPt_JFr_TX2_Slot11_2
import RPt_JFr_TX2_Slot11_3
import RPt_JFr_TX2_Slot12_0
import RPt_JFr_TX2_Slot12_1
import RPt_JFr_TX2_Slot12_2
import RPt_JFr_TX2_Slot12_3
import RPt_JFr_TX2_Slot13_0
import RPt_JFr_TX2_Slot13_1
import RPt_JFr_TX2_Slot13_2
import RPt_JFr_TX2_Slot13_3
import RPt_JFr_TX2_Slot14_0
import RPt_JFr_TX2_Slot14_1
import RPt_JFr_TX2_Slot14_2
import RPt_JFr_TX2_Slot14_3
import RPt_JFr_TX2_Slot15_0
import RPt_JFr_TX2_Slot15_1
import RPt_JFr_TX2_Slot15_2
import RPt_JFr_TX2_Slot15_3
import RPt_JFr_TX2_Slot16_0
import RPt_JFr_TX2_Slot16_1
import RPt_JFr_TX2_Slot16_2
import RPt_JFr_TX2_Slot16_3
import RPt_JFr_TX2_Slot17_0
import RPt_JFr_TX2_Slot17_1
import RPt_JFr_TX2_Slot17_2
import RPt_JFr_TX2_Slot17_3
import RPt_JFr_TX2_Slot18_0
import RPt_JFr_TX2_Slot18_1
import RPt_JFr_TX2_Slot18_2
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPt_JFq_Sem07, `RPt_JFq_Sem08, `RPt_JFq_Sem09, `RPt_JFq_Semantic, `RPt_JFq_Z0, `RPt_JFq_Z1, `RPt_JFq_Z2, `RPt_JFq_Z3, `RPt_JFq_Claim, `RPt_JFq_Rhs, `RPt_JFq_Power, `RPt_JFq_Weights00, `RPt_JFq_Weights01, `RPt_JFq_Weights02, `RPt_JFq_Weights03, `RPt_JFq_Weights04, `RPt_JFq_Weights05, `RPt_JFq_Weights06, `RPt_JFq_Weights07, `RPt_JFq_Weights08, `RPt_JFq_Weights09, `RPt_JFq_Weights10, `RPt_JFq_Weights11, `RPt_JFq_Weights12, `RPt_JFq_Weights13, `RPt_JFq_Weights14, `RPt_JFq_Weights15, `RPt_JFq_ReadSequence, `RPt_JFq_WeightReads, `RPt_JFo_WeightRestore, `RPt_JFo_Weights, `RPt_JFo_Prepared, `RPt_JFo_Opening, `RPt_JFo_QueryRead, `RPt_JFn_FieldRead, `RPt_JFn_ValueBlock, `RPt_JFo_PrefixRead, `RPt_JFr_TX2_Windows, `RPt_JFr_TX2_ScalarRead, `RPt_JFr_TX2_DotStep, `RPt_JFr_TX2_DotLanes, `RPt_JFr_TX2_DotBounds, `RPt_JFr_TX2_DotLaneTotal, `RPt_FJi_LaneValue, `RPt_FJi_Coordinate0, `RPt_FJi_Coordinate1, `RPt_FJi_Coordinate2, `RPt_FJi_Coordinate3, `RPt_FJi_Coordinate4, `RPt_FJi_Coordinate5, `RPt_FJi_Coordinate6, `RPt_FJi_Coordinate7, `RPt_FJi_EightValue, `RPt_FJi_Inputs, `RPt_FJi_TermValue, `RPt_FJi_InnerStep, `RPt_FJi_InnerValue, `RPt_JFs_TX2_Eight, `RPt_JFs_TX2_ArrayEight, `RPt_JFv_TX2_ArrayMeaning, `RPt_JFs_TX2_FoldLane, `RPt_JFs_TX2_FoldEight, `RPt_JFv_TX2_FoldMeaning, `RPt_JFv_TX2_FoldValue, `RPt_JFr_TX2_DecodeCell, `RPt_JFr_TX2_Slot10_0, `RPt_JFr_TX2_Slot10_1, `RPt_JFr_TX2_Slot10_2, `RPt_JFr_TX2_Slot10_3, `RPt_JFr_TX2_Slot11_0, `RPt_JFr_TX2_Slot11_1, `RPt_JFr_TX2_Slot11_2, `RPt_JFr_TX2_Slot11_3, `RPt_JFr_TX2_Slot12_0, `RPt_JFr_TX2_Slot12_1, `RPt_JFr_TX2_Slot12_2, `RPt_JFr_TX2_Slot12_3, `RPt_JFr_TX2_Slot13_0, `RPt_JFr_TX2_Slot13_1, `RPt_JFr_TX2_Slot13_2, `RPt_JFr_TX2_Slot13_3, `RPt_JFr_TX2_Slot14_0, `RPt_JFr_TX2_Slot14_1, `RPt_JFr_TX2_Slot14_2, `RPt_JFr_TX2_Slot14_3, `RPt_JFr_TX2_Slot15_0, `RPt_JFr_TX2_Slot15_1, `RPt_JFr_TX2_Slot15_2, `RPt_JFr_TX2_Slot15_3, `RPt_JFr_TX2_Slot16_0, `RPt_JFr_TX2_Slot16_1, `RPt_JFr_TX2_Slot16_2, `RPt_JFr_TX2_Slot16_3, `RPt_JFr_TX2_Slot17_0, `RPt_JFr_TX2_Slot17_1, `RPt_JFr_TX2_Slot17_2, `RPt_JFr_TX2_Slot17_3, `RPt_JFr_TX2_Slot18_0, `RPt_JFr_TX2_Slot18_1, `RPt_JFr_TX2_Slot18_2 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPT_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPT_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPT_AUDIT_COMPLETE declarations={count} modules={selected.size}"

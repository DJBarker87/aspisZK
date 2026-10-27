import Lean
import RPt_JFr_TX2_Slot18_3
import RPt_JFr_TX2_Slot19_0
import RPt_JFr_TX2_Slot19_1
import RPt_JFr_TX2_Slot19_2
import RPt_JFr_TX2_Slot19_3
import RPt_JFr_TX2_Slot20_0
import RPt_JFr_TX2_Slot20_1
import RPt_JFr_TX2_Slot20_2
import RPt_JFr_TX2_Slot20_3
import RPt_JFr_TX2_Slot21_0
import RPt_JFr_TX2_Slot21_1
import RPt_JFr_TX2_Slot21_2
import RPt_JFr_TX2_Slot21_3
import RPt_JFr_TX2_ScalarCanon
import RPt_JFo_Index
import RPt_JFo_QueryIndex
import RPt_JFn_Value10_0
import RPt_JFn_Value10_1
import RPt_JFn_Value10_2
import RPt_JFn_Value10_3
import RPt_JFn_ArrayBuilder
import RPt_JFn_Values10
import RPt_JFn_Value11_0
import RPt_JFn_Value11_1
import RPt_JFn_Value11_2
import RPt_JFn_Value11_3
import RPt_JFn_Values11
import RPt_JFn_Value12_0
import RPt_JFn_Value12_1
import RPt_JFn_Value12_2
import RPt_JFn_Value12_3
import RPt_JFn_Values12
import RPt_JFn_Value13_0
import RPt_JFn_Value13_1
import RPt_JFn_Value13_2
import RPt_JFn_Value13_3
import RPt_JFn_Values13
import RPt_JFn_Value14_0
import RPt_JFn_Value14_1
import RPt_JFn_Value14_2
import RPt_JFn_Value14_3
import RPt_JFn_Values14
import RPt_JFn_Value15_0
import RPt_JFn_Value15_1
import RPt_JFn_Value15_2
import RPt_JFn_Value15_3
import RPt_JFn_Values15
import RPt_JFn_Value16_0
import RPt_JFn_Value16_1
import RPt_JFn_Value16_2
import RPt_JFn_Value16_3
import RPt_JFn_Values16
import RPt_JFn_Value17_0
import RPt_JFn_Value17_1
import RPt_JFn_Value17_2
import RPt_JFn_Value17_3
import RPt_JFn_Values17
import RPt_JFn_Value18_0
import RPt_JFn_Value18_1
import RPt_JFn_Value18_2
import RPt_JFn_Value18_3
import RPt_JFn_Values18
import RPt_JFn_Value19_0
import RPt_JFn_Value19_1
import RPt_JFn_Value19_2
import RPt_JFn_Value19_3
import RPt_JFn_Values19
import RPt_JFn_Value20_0
import RPt_JFn_Value20_1
import RPt_JFn_Value20_2
import RPt_JFn_Value20_3
import RPt_JFn_Values20
import RPt_JFn_Value21_0
import RPt_JFn_Value21_1
import RPt_JFn_Value21_2
import RPt_JFn_Value21_3
import RPt_JFn_Values21
import RPt_JFn_Values
import RPt_JFr_TX2_Scalars
import RPt_JFr_TX2_DotTerm
import RPt_JFo_GammaCanonical
import RPt_JFo_Powers
import RPt_JFr_TX2_Powers
import RPt_JFr_TX2_FirstLane
import RPt_JFs_TX2_ArrayRead
import RPt_JFs_TX2_Update
import RPt_JFs_TX2_Term
import RPt_JFs_TX2_Inner
import RPt_JFs_TX2_Iterator
import RPt_JFs_TX2_OuterStep
import RPt_JFs_TX2_BatchWindow
import RPt_JFs_TX2_OuterActive
import RPt_FJi_OuterTerm
import RPt_FJi_OuterStep
import RPt_FJi_OuterValue
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPt_JFr_TX2_Slot18_3, `RPt_JFr_TX2_Slot19_0, `RPt_JFr_TX2_Slot19_1, `RPt_JFr_TX2_Slot19_2, `RPt_JFr_TX2_Slot19_3, `RPt_JFr_TX2_Slot20_0, `RPt_JFr_TX2_Slot20_1, `RPt_JFr_TX2_Slot20_2, `RPt_JFr_TX2_Slot20_3, `RPt_JFr_TX2_Slot21_0, `RPt_JFr_TX2_Slot21_1, `RPt_JFr_TX2_Slot21_2, `RPt_JFr_TX2_Slot21_3, `RPt_JFr_TX2_ScalarCanon, `RPt_JFo_Index, `RPt_JFo_QueryIndex, `RPt_JFn_Value10_0, `RPt_JFn_Value10_1, `RPt_JFn_Value10_2, `RPt_JFn_Value10_3, `RPt_JFn_ArrayBuilder, `RPt_JFn_Values10, `RPt_JFn_Value11_0, `RPt_JFn_Value11_1, `RPt_JFn_Value11_2, `RPt_JFn_Value11_3, `RPt_JFn_Values11, `RPt_JFn_Value12_0, `RPt_JFn_Value12_1, `RPt_JFn_Value12_2, `RPt_JFn_Value12_3, `RPt_JFn_Values12, `RPt_JFn_Value13_0, `RPt_JFn_Value13_1, `RPt_JFn_Value13_2, `RPt_JFn_Value13_3, `RPt_JFn_Values13, `RPt_JFn_Value14_0, `RPt_JFn_Value14_1, `RPt_JFn_Value14_2, `RPt_JFn_Value14_3, `RPt_JFn_Values14, `RPt_JFn_Value15_0, `RPt_JFn_Value15_1, `RPt_JFn_Value15_2, `RPt_JFn_Value15_3, `RPt_JFn_Values15, `RPt_JFn_Value16_0, `RPt_JFn_Value16_1, `RPt_JFn_Value16_2, `RPt_JFn_Value16_3, `RPt_JFn_Values16, `RPt_JFn_Value17_0, `RPt_JFn_Value17_1, `RPt_JFn_Value17_2, `RPt_JFn_Value17_3, `RPt_JFn_Values17, `RPt_JFn_Value18_0, `RPt_JFn_Value18_1, `RPt_JFn_Value18_2, `RPt_JFn_Value18_3, `RPt_JFn_Values18, `RPt_JFn_Value19_0, `RPt_JFn_Value19_1, `RPt_JFn_Value19_2, `RPt_JFn_Value19_3, `RPt_JFn_Values19, `RPt_JFn_Value20_0, `RPt_JFn_Value20_1, `RPt_JFn_Value20_2, `RPt_JFn_Value20_3, `RPt_JFn_Values20, `RPt_JFn_Value21_0, `RPt_JFn_Value21_1, `RPt_JFn_Value21_2, `RPt_JFn_Value21_3, `RPt_JFn_Values21, `RPt_JFn_Values, `RPt_JFr_TX2_Scalars, `RPt_JFr_TX2_DotTerm, `RPt_JFo_GammaCanonical, `RPt_JFo_Powers, `RPt_JFr_TX2_Powers, `RPt_JFr_TX2_FirstLane, `RPt_JFs_TX2_ArrayRead, `RPt_JFs_TX2_Update, `RPt_JFs_TX2_Term, `RPt_JFs_TX2_Inner, `RPt_JFs_TX2_Iterator, `RPt_JFs_TX2_OuterStep, `RPt_JFs_TX2_BatchWindow, `RPt_JFs_TX2_OuterActive, `RPt_FJi_OuterTerm, `RPt_FJi_OuterStep, `RPt_FJi_OuterValue ]
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

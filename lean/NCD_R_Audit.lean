import Lean
import NCD_R_JFr_TX2_Tails
import NCD_R_JFs_TX2_TailStages
import NCD_R_JFs_TX2_WideAdd
import NCD_R_NBS_DotTerm
import NCD_R_NBS_DotInner
import NCD_R_NBS_DotOuterActive
import NCD_R_NBS_DotOuter
import NCD_R_NBS_DotTail
import NCD_R_NBS_DotWhole
import NCD_R_NBS_PowersCanon
import NCD_R_NBS_Four
import NCD_R_NBS_NativeEight
import NCD_R_NCB_CoefficientDomains
import NCD_R_NCB_DotNativeStep
import NCD_R_NCB_ScalarDomains
import NCD_R_NCB_TailOffsets
import NCD_R_NCB_TailDomains
import NCD_R_NCB_FourDomains
import NCD_R_NCB_TailFinal
import NCB_ResizeStep
import NCB_Filled14759
import NCB_DigestTotal
import NCB_PrefixNativeStep
import NCB_PrefixCutTrace
import NCB_ChronologicalBlock
import NCD_GeometryCutDomains
import NCD_FillFrame
#print axioms NCB_ResizeStep.next
#print axioms NCB_Filled14759.model
#print axioms NCB_Filled14759.selected
#print axioms AspisR1.NCB_DigestTotal.total
#print axioms AspisR1.NCB_DigestTotal.reached
#print axioms NCB_ScalarDomains.accepted
#print axioms NCB_TailOffsets.first
#print axioms NCB_TailOffsets.second
#print axioms NCB_TailOffsets.third
#print axioms NCB_DotNativeStep.source
#print axioms NCB_PrefixNativeStep.source
#print axioms NCB_PrefixNativeStep.stopped
#print axioms NCB_TailDomains.accepted
#print axioms NCB_CoefficientDomains.returned
#print axioms NCB_PrefixCutTrace.associated
#print axioms NCB_PrefixCutTrace.meaning
#print axioms NCB_FourDomains.accepted
#print axioms NCB_TailFinal.source
#print axioms AspisR1.NCB_ChronologicalBlock.construct
#print axioms AspisR1.NCB_ChronologicalBlock.observed
#print axioms NCD_GeometryCutDomains.aligned
#print axioms NCD_FillFrame.initialized14759
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"NCD_IMPORTS {(Json.mkObj [("module", toJson m.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"

import NCD_FillFrame
import NCD_FillAssociation
import NCD_GeometryCutDomains
import NCD_ChronologicalQuery
import NCD_QueryFrame
import NCD_DotCutTrace
import Lean
-- Inherited co-import audit; no theorem bodies are reproved.
import NCD_B_NBS_Audit
import NCD_B_NBQ_Audit
import NCD_B_NCB_ResizeStep
import NCD_B_NCB_Filled14759
import NCD_B_NCB_DigestTotal
import NCD_R_NCB_ScalarDomains
import NCD_R_NCB_TailOffsets
import NCD_R_NCB_DotNativeStep
import NCD_B_NCB_PrefixNativeStep
import NCD_R_NCB_TailDomains
import NCD_R_NCB_CoefficientDomains
import NCD_B_NCB_PrefixCutTrace
import NCD_R_NCB_FourDomains
import NCD_R_NCB_TailFinal
import NCD_B_NCB_ChronologicalBlock
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

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"NCD_IMPORTS {(Json.mkObj [("module", toJson m.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"

#print axioms NCD_FillFrame.metadata
#print axioms NCD_FillFrame.storage
#print axioms NCD_FillFrame.initialized14759
#print axioms NCD_FillAssociation.contents
#print axioms NCD_FillAssociation.model14759
#print axioms NCD_GeometryCutDomains.aligned
#print axioms AspisR1.NCD_ChronologicalQuery.materialized
#print axioms AspisR1.NCD_QueryFrame.materialized
#print axioms NCD_DotCutTrace.associated

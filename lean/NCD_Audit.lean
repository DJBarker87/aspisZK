import Lean
-- Inherited co-import audit; no theorem bodies are reproved.
import NBS_Audit
import NBQ_Audit
import NCB_ResizeStep
import NCB_Filled14759
import NCB_DigestTotal
import NCB_ScalarDomains
import NCB_TailOffsets
import NCB_DotNativeStep
import NCB_PrefixNativeStep
import NCB_TailDomains
import NCB_CoefficientDomains
import NCB_PrefixCutTrace
import NCB_FourDomains
import NCB_TailFinal
import NCB_ChronologicalBlock
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

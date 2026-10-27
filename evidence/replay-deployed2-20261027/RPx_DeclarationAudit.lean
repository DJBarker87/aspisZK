import Lean
import RPx_FIr_FinishComparison
import RPx_FIr_AcceptedTerminal
import RPx_FJn_MaskC1Gather
import RPx_FJq_MaskC1Callback
import RPx_FJq_ClaimZero
import RPx_FJq_MaskC1Value
import RPx_FJq_MaskOnlyCallback
import RPx_FJq_MaskOnlyValue
import RPx_FJn_MaskOnlyGather
import RPx_FJq_MaskedSourceFormula
import RPx_FJq_MaskedMain
import RPx_FJq_ExtraCanonical
import RPx_FJq_AcceptedExtra
import RPx_FJt_AcceptedMaskedMain
import RPx_FJq_AcceptedLiteralRows
import RPx_FJq_MaskedLiteral
import RPx_FJt_AcceptedMaskedLiteral
import RPx_FJt_Endpoint
import RPx_FJt_RunEndpoint
import RPx_FJt_GlobalTerminal
import RPx_FJv_GlobalTerminal
import RPx_FJt_NativeDiscovery
import RPx_FJt_NativeAttach
import RPx_FJt_SourceConsumer
import RPx_FJv_DLiteral
import RPx_FJv_DDefinitions
import RPx_FJv_DNativePair
import RPx_FJv_DFinalSource
import RPx_FJv_DCont
import RPx_FJv_DCaller
import RPx_FJv_DR5Close
import RPx_FJv_DBoundCaller
import RPx_FJv_DR6Caller
import RPx_FJv_DR6Result
import RPx_FJv_DRelease
import RPx_FJv_DNativeAccepted
import RPx_Deployed
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPx_FIr_FinishComparison, `RPx_FIr_AcceptedTerminal, `RPx_FJn_MaskC1Gather, `RPx_FJq_MaskC1Callback, `RPx_FJq_ClaimZero, `RPx_FJq_MaskC1Value, `RPx_FJq_MaskOnlyCallback, `RPx_FJq_MaskOnlyValue, `RPx_FJn_MaskOnlyGather, `RPx_FJq_MaskedSourceFormula, `RPx_FJq_MaskedMain, `RPx_FJq_ExtraCanonical, `RPx_FJq_AcceptedExtra, `RPx_FJt_AcceptedMaskedMain, `RPx_FJq_AcceptedLiteralRows, `RPx_FJq_MaskedLiteral, `RPx_FJt_AcceptedMaskedLiteral, `RPx_FJt_Endpoint, `RPx_FJt_RunEndpoint, `RPx_FJt_GlobalTerminal, `RPx_FJv_GlobalTerminal, `RPx_FJt_NativeDiscovery, `RPx_FJt_NativeAttach, `RPx_FJt_SourceConsumer, `RPx_FJv_DLiteral, `RPx_FJv_DDefinitions, `RPx_FJv_DNativePair, `RPx_FJv_DFinalSource, `RPx_FJv_DCont, `RPx_FJv_DCaller, `RPx_FJv_DR5Close, `RPx_FJv_DBoundCaller, `RPx_FJv_DR6Caller, `RPx_FJv_DR6Result, `RPx_FJv_DRelease, `RPx_FJv_DNativeAccepted, `RPx_Deployed ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPX_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPX_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPX_AUDIT_COMPLETE declarations={count} modules={selected.size}"

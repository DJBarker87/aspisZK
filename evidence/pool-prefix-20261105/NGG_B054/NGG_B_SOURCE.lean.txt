import Lean
import NFR_WALKER
import NFR_MemoryLimit
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFO_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) := if mode == "final" then
    (#[`NFV_PoolReturnData,`NGG_Count,`NGG_Loader,`NGG_Compare,`NGG_Metadata,`NGG_Payer,`NGG_Transport,`NGG_Scalar,`NGG_LayoutValue,`NGG_DecodePrefix,`NGG_RequestLength,`NGG_LayoutBounds,`NGG_PaymentWindows,`NGG_EnvelopePrefix,`NGG_MarkerZero,`NGG_ErrorImage],
     #[`NFR_ModelJoin.same_emitted_settlement,`NGG_Count.result,`NGG_Loader.result,`NGG_Compare.ne,`NGG_Metadata.verifier,`NGG_Metadata.token,`NGG_Payer.result,`NGG_Transport.result,`NGG_Scalar.wrapping_add,`NGG_Scalar.checked_add,`NGG_LayoutGTransfer.result,`NGG_LayoutGWithdrawal.result,`NGG_LayoutRTransfer.result,`NGG_LayoutRWithdrawal.result,`NGG_LayoutValue.result,`NGG_LayoutBounds.metas,`NGG_LayoutBounds.windows,`NGG_DecodePrefix.resume_eq,`NGG_DecodePrefix.cut,`NGG_RequestLength.decoder,`NGG_RequestLength.payload,`NGG_PaymentWindows.point,`NGG_PaymentWindows.domain,`NGG_EnvelopePrefix.asq8,`NGG_MarkerZero.predicate,`NGG_MarkerZero.value,`NGG_MarkerZero.bound,`NGG_MarkerZero.abort,`NGG_ErrorImage.failure,`NGG_ErrorImage.success])
    else if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  let ctx : Command.Context := {
    fileName := "NEP_Driver"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  let action : CommandElabM Bool := do
    let mut failed := false
    for root in roots do
      try
        elabCommand (← `(command| #print axioms $(mkIdent root)))
        NEP.audit root ("NEP_" ++ mode ++ "_" ++ root.toString)
      catch e =>
        logError e.toMessageData
        failed := true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0

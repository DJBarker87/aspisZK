import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command

/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    if mode == "proof0" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_Advance.accepted, `AspisR1.NFP_Carrier.from_to, `AspisR1.NFP_Carrier.to_from, `AspisR1.NFP_Carrier.words, `AspisR1.NFP_Carrier.canonical, `AspisR1.NFP_DotCaller.tail, `AspisR1.NFP_DotCaller.query, `AspisR1.NFP_DotDomains.returned, `AspisR1.NFP_DotInstall.dot_result])
    else if mode == "proof1" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_DotInstall.head, `AspisR1.NFP_FrameExt.raw, `AspisR1.NFP_GeometryDomains.reads, `AspisR1.NFP_HeadDomain.reached, `AspisR1.NFP_LoopBudget.tx1, `AspisR1.NFP_LoopBudget.tx2, `AspisR1.NFP_LoopBudget.maximum, `AspisR1.NFP_LoopTerminals.error])
    else if mode == "proof2" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_LoopTerminals.stopped, `AspisR1.NFP_LoopTerminals.rejected, `AspisR1.NFP_LoopTerminals.failed, `AspisR1.NFP_LoopTerminals.diverged, `AspisR1.NFP_LoopTransport.child, `AspisR1.NFP_LoopTransport.complete, `AspisR1.NFP_NatBase.sub_word, `AspisR1.NFP_NatBase.add])
    else if mode == "proof3" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_NatBase.sub, `AspisR1.NFP_NodeDictionary.product, `AspisR1.NFP_NodeDictionary.add, `AspisR1.NFP_NodeDictionary.sub, `AspisR1.NFP_NodeDictionary.node, `AspisR1.NFP_ObserverErasure.query, `AspisR1.NFP_ObserverErasure.phase, `AspisR1.NFP_ObserverErasure.trace])
    else if mode == "proof4" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_ProductLaw.emitted, `AspisR1.NFP_ProductLaw.node, `AspisR1.NFP_QueryAdvance.accepted, `AspisR1.NFP_QueryAdvance.offset, `AspisR1.NFP_QueryCuts.source, `AspisR1.NFP_QueryTrace.erased, `AspisR1.NFP_RejectionTrace.guard, `AspisR1.NFP_RejectionTrace.rejected_prefix])
    else if mode == "proof5" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_Resume.tx1, `AspisR1.NFP_Resume.tx2, `AspisR1.NFP_ReturnCuts.erased, `AspisR1.NFP_ReturnCuts.continuation, `AspisR1.NFP_SuffixCuts.source, `AspisR1.NFP_TraceBack.erased, `AspisR1.NFP_TraceFront.erased, `AspisR1.NFP_TraceHead.erased])
    else if mode == "proof6" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFP_TraceTypes.pure_result, `AspisR1.RPx_Deployed.deployed, `AspisR1.NFM_ProductInstance.installed, `AspisR1.NFM_ProductInstance.wrapper, `AspisR1.NFM_Cuts.abort_prefix, `AspisR1.NFG_QueryLoopSource.complete, `AspisR1.NFG_PushRoot.private_result, `AspisR1.NFG_PushRoot.public_result])
    else if mode == "extra" then
      (#[`NFP_CombinedFinal], #[`AspisR1.NFM_Single.domains, `AspisR1.NFG_PushRoot.private_domains])
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

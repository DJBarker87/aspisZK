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
  let (modules, roots) := if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[`NHL_COMBINED_IMPORT], #[`AspisR1.NHL_BindOn.reached,
      `AspisR1.NHL_BorrowWindows.left,
      `AspisR1.NHL_BorrowWindows.right,
      `AspisR1.NHL_DriverModel.source,
      `AspisR1.NHL_DriverSlots.prepare,
      `AspisR1.NHL_DriverSlots.tx1,
      `AspisR1.NHL_EmittedPrepare.prepare,
      `AspisR1.NHL_EmittedTx1.tx1,
      `AspisR1.NHL_HeapPacket.accepted,
      `AspisR1.NHL_HeapPacket.rejected,
      `AspisR1.NHL_OpeningPacket.Fold,
      `AspisR1.NHL_OpeningPacket.Packet,
      `AspisR1.NHL_OpeningPacket.fold_fields,
      `AspisR1.NHL_OpeningPacket.fold_result,
      `AspisR1.NHL_OpeningPacket.gamma_canonical,
      `AspisR1.NHL_OpeningPacket.increment,
      `AspisR1.NHL_OpeningPacket.kappa_canonical,
      `AspisR1.NHL_OpeningPacket.result,
      `AspisR1.NHL_Packets.installed,
      `AspisR1.NHL_PrefixPacket.accepted,
      `AspisR1.NHL_PrefixPacket.rejected,
      `AspisR1.NHL_PrepareDomain.reached,
      `AspisR1.NHL_PrepareEq.logical_add,
      `AspisR1.NHL_PrepareEq.source,
      `AspisR1.NHL_PrepareModel.buffers_children,
      `AspisR1.NHL_PrepareModel.source,
      `AspisR1.NHL_PrepareModel.source_constants,
      `AspisR1.NHL_PrepareModel.target_constants,
      `AspisR1.NHL_PrepareStages.buffers,
      `AspisR1.NHL_PrepareStages.factor,
      `AspisR1.NHL_PrepareStages.run,
      `AspisR1.NHL_PreparedClaim.claim,
      `AspisR1.NHL_PreparedFailures.query_div,
      `AspisR1.NHL_PreparedFailures.query_fail,
      `AspisR1.NHL_PreparedOpening.double,
      `AspisR1.NHL_PreparedOpening.double_factor,
      `AspisR1.NHL_PreparedOpening.prefix_result,
      `AspisR1.NHL_PreparedOpening.single,
      `AspisR1.NHL_PreparedRecompose.query_error,
      `AspisR1.NHL_PreparedRecompose.source,
      `AspisR1.NHL_PreparedScalars.alpha0,
      `AspisR1.NHL_PreparedScalars.gamma,
      `AspisR1.NHL_PreparedScalars.kappa,
      `AspisR1.NHL_PreparedScalars.rho,
      `AspisR1.NHL_PreparedScalars.rho_dictionary,
      `AspisR1.NHL_PreparedScalars.scalar_dictionary,
      `AspisR1.NHL_QueryDomain.dictionary,
      `AspisR1.NHL_QueryDomain.emitted,
      `AspisR1.NHL_QueryInterface.dictionary,
      `AspisR1.NHL_QueryInterface.result,
      `AspisR1.NHL_SplitPacket.sizes,
      `AspisR1.NHL_Tx1Eq.source,
      `AspisR1.NHL_Tx1Model.before_children,
      `AspisR1.NHL_Tx1Model.before_prepare,
      `AspisR1.NHL_Tx1Model.source,
      `AspisR1.NHL_Tx1Stages.Context,
      `AspisR1.NHL_Tx1Stages.beforeQuery,
      `AspisR1.NHL_Tx1Stages.factor,
      `AspisR1.NHL_Tx1Stages.run,
      `AspisR1.NHL_ValuesPacket.accepted,
      `AspisR1.NHL_ValuesPacket.length,
      `AspisR1.RPx_Deployed.deployed])
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

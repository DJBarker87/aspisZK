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
    else if mode == "proof0" then
      (#[`NLP_COMBINED_IMPORT], #[`NLP_Assembly.installed, `NLP_C01.native_scope, `NLP_C01.step, `NLP_C04All.source, `NLP_C04AtActual.packet, `NLP_C04Chronology.fold, `NLP_C04Chronology.at_actual, `NLP_C04Effects.returning, `NLP_C04Effects.aborting, `NLP_C04Folded.source, `NLP_C04Folded.at_actual, `NLP_C04Query.domain])
    else if mode == "proof1" then
      (#[`NLP_COMBINED_IMPORT], #[`NLP_C04Query.packet, `NLP_C04Reply.relation, `NLP_C04Reply.at_actual, `NLP_C04Roots.bindings, `NLP_C04Trees.packet, `NLP_EffectOrder.append, `NLP_EffectOrder.prefix_frame, `NLP_EffectOrder.congr, `NLP_EnteredTransport.source, `NLP_FoldedRange.diff, `NLP_FoldedRange.start, `NLP_FoldedRange.selected])
    else if mode == "proof2" then
      (#[`NLP_COMBINED_IMPORT], #[`NLP_FoldedRange.copied, `NLP_FoldedValue.source, `NLP_InputCounterexample.distinct, `NLP_InputCounterexample.different, `NLP_InputCounterexample.middle, `NLP_InputCounterexample.length, `NLP_InputCounterexample.projection, `NLP_InputCounterexample.extents_insufficient, `NLP_NativeFold.installed, `NLP_ResumeInstall.packet, `NLP_ResumeInstall.scope, `NLP_ResumeInstall.action])
    else if mode == "proof3" then
      (#[`NLP_COMBINED_IMPORT], #[`NLP_ResumeRoots.returned, `NLP_RootCodec.decode_array, `NLP_RootCodec.wire, `NLP_RootCodec.kind1, `NLP_RootDomain.kind0_fixed, `NLP_RootDomain.necessary, `NLP_RootDomain.mismatch, `NLP_TransportDomain.at_branch, `NLB_Parent.native_fold, `NKU_ParentFold.source, `NKU_ParentFold.cohort, `NKU_ParentFold.clauses])
    else if mode == "proof4" then
      (#[`NLP_COMBINED_IMPORT], #[`NLN_TX2_053.root, `AspisR1.RPx_Deployed.deployed])
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

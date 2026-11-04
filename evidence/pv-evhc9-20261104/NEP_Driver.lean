import Lean
import NEP_WALKER
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) := if mode == "final" then
    (#[`PV_BR_FixtureConsumer, `RPx_Deployed, `NDR_CombinedAudit],
     #[`PV_EVH_FixtureConsumer.deployedInstance,
       `PV_EVH_FixtureConsumer.instance_nonvacuity,
       `PV_EVH_FixtureConsumer.public_fibre,
       `PV_EVH_FixtureConsumer.two_transaction_nonvacuity,
       `PV_BR_Transport.payment_left_inverse,
       `PV_BR_Transport.payment_right_inverse,
       `PV_BR_Transport.payment_discriminant,
       `PV_BR_Transport.payment_injective,
       `PV_BR_Transport.tree_left_inverse,
       `PV_BR_Transport.tree_right_inverse,
       `PV_BR_Transport.tree_discriminant,
       `PV_BR_Transport.tree_injective,
       `PV_BR_Transport.verifier_retraction,
       `PV_BR_Transport.verifier_join_split,
       `PV_BR_Transport.verifier_split_join,
       `PV_BR_Transport.verifier_embedding_injective,
       `PV_BR_Transport.verifier_discriminant,
       `PV_BR_Transport.mapCoreError_inverse,
       `PV_BR_Transport.payment_result_transport,
       `PV_BR_Transport.tree_result_transport,
       `PV_BR_AdmissionTransport.prover_run_roundtrip,
       `PV_BR_AdmissionTransport.from_to,
       `PV_BR_AdmissionTransport.to_from,
       `PV_BR_AdmissionTransport.mapRunError_inverse,
       `PV_BR_AdmissionTransport.mapRunError_success,
       `PV_BR_AdmissionTransport.validateCommon_roundtrip,
       `PV_BR_AdmissionTransport.validateCommon_success,
       `R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed,
       `R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events,
       `R1Z.PV_RJ4IDB_CallerLive.caller_witness,
       `AspisR1.NDR_CombinedAudit.sourceOnHeadline,
       `AspisR1.RPx_Deployed.deployed])
    else if mode == "fixtures" then
    (#[`NEP_Planted, `NEP_Mutations, `PV_D595_Cases],
     #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
       `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
       `NEP_MutateProof.proof, `NEP_MutateAux.viaAux,
       `PV_D595_Cases.payload, `PV_D595_Cases.proof])
    else (#[`NEP_Planted], #[`PV_D595_Cases.deliberatelyMissing])
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

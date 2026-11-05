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
      (#[`NHV_COMBINED_IMPORT], #[`AspisR1.LPf_BaseMultiply.source, `AspisR1.LPf_WideConstruction.source, `AspisR1.LPi_FieldValues.cm_mul, `AspisR1.LPi_MixedValues.cm_m31, `AspisR1.LPi_MixedValues.qm_m31, `AspisR1.LPi_TowerValues.mul_u, `AspisR1.LPi_TowerValues.qm_mul, `AspisR1.LPi_TowerValues.wide_mul, `NBG_FieldDischarge.canonical_fio, `NBG_FieldDischarge.wide_qm, `NBG_FieldDischarge.wide_scale, `NBG_WideBytes.bytes_result, `NBG_WideCarriers.canonical_qm31, `NBG_WideCarriers.limbs_result, `NBG_WideCarriers.remainder, `NBG_WideCarriers.to_limbs_result, `NBG_WideCarriers.wide_add, `NBG_WideCarriers.wide_new, `NBG_WideCarriers.wrong_byte_length, `NEB_ArrayRefs.cm_add])
    else if mode == "proof1" then
      (#[`NHV_COMBINED_IMPORT], #[`NEB_ArrayRefs.cm_injective, `NEB_ArrayRefs.cm_sub, `NEB_ArrayRefs.qm_add, `NEB_ArrayRefs.qm_injective, `NEB_ArrayRefs.qm_sub, `NEB_ArrayRefs.wide_add, `NEB_ArrayRefs.wide_injective, `NEB_BaseCallBounds.add, `NEB_BaseCallBounds.multiply_reducer, `NEB_BaseCallBounds.raw_product, `NEB_BaseCallBounds.reducer, `NEB_BaseCallBounds.reducer_wrapper, `NEB_BaseCallBounds.sub, `NEB_CMCalls.multiply, `NEB_CMCalls.scale, `NEB_FieldDomains.cm_add_calls, `NEB_FieldDomains.cm_arguments, `NEB_FieldDomains.cm_cross_arguments, `NEB_FieldDomains.cm_sub_calls, `NEB_FieldDomains.qm_arguments])
    else if mode == "proof2" then
      (#[`NHV_COMBINED_IMPORT], #[`NEB_FieldDomains.wide_arguments, `NEB_WordRefs.add, `NEB_WordRefs.double, `NEB_WordRefs.normalize, `NEB_WordRefs.normalize_value, `NEB_WordRefs.sub, `NEO_ByteCuts.complex, `NEO_ByteCuts.conversion, `NEO_ByteCuts.residual, `NEO_ByteCuts.scalar, `NEO_ComplexCells.first, `NEO_ComplexCells.second, `NEO_ComplexCells.small, `NEO_ComplexCells.word0, `NEO_ComplexCells.word4, `NEO_ComplexReference.eight, `NEO_ComplexTotal.eight, `NEO_ComplexTotal.fixed, `NEO_ComplexTotal.observe_injective, `NEO_ComplexTotal.result])
    else if mode == "proof3" then
      (#[`NHV_COMBINED_IMPORT], #[`NEO_FieldView.addresses, `NEO_FieldView.result, `NEO_FixedWindow.range, `NEO_ParserReference.limbs, `NEO_ParserReference.scalar, `NEO_ParserShapes.limbs_result, `NEO_ParserShapes.scalar_result, `NEO_ParserShapes.wide_observation_injective, `NEO_ParserTotal.eight, `NEO_ParserTotal.option_lossless, `NEO_ParserTotal.result, `NEO_PrefixSlices.complex, `NEO_PrefixSlices.range, `NEO_QModelBinding.complex, `NEO_QModelBinding.quadratic, `NEO_QuadraticCuts.result, `NEO_QuadraticTotal.complex_frame, `NEO_QuadraticTotal.observe_injective, `NEO_QuadraticTotal.quadratic_frame, `NEO_QuadraticTotal.result])
    else if mode == "proof4" then
      (#[`NHV_COMBINED_IMPORT], #[`NEO_WideReference.fixed, `NEO_WideReference.result, `NEO_WideTotal.frame, `NEO_WideTotal.option_lossless, `NEO_WideTotal.result, `NEO_WideTotal.wrong_length, `NEO_WideWord.fixed, `NEO_WideWord.small, `NEO_WindowFrame.length, `NEO_WindowFrame.outside, `NEO_WindowFrame.rebase, `NEO_WindowFrame.selected, `NEO_WindowFrame.subwindow, `NEO_WindowPrefix.complex, `NEO_WindowPrefix.index, `NEO_WindowPrefix.word, `NEO_WindowPrefix.wrap_small, `NET_ParserComposed.c_roundtrip, `NET_ParserComposed.complex_result, `NET_ParserComposed.complex_result_state_effects])
    else if mode == "proof5" then
      (#[`NHV_COMBINED_IMPORT], #[`NET_ParserComposed.q_roundtrip, `NET_ParserComposed.quadratic_result, `NET_ParserComposed.quadratic_result_state_effects, `NET_WideModel.result, `NET_WideModel.result_state_effects, `NET_WideModel.roundtrip, `NHV_InactivePacket.exact_window, `NHV_InactivePacket.reject, `NHV_InactivePacket.source, `NHV_NativeOps.forget_run, `NHV_NativeOps.geometry_result, `NHV_NativeOps.pending_reply, `NHV_NativeOps.slots, `NHV_NativeOps.source, `NHV_PendingPacket.raw_same, `NHV_PendingPacket.returned, `NHV_PendingPacket.source, `NHV_ReleaseOps.open_fields, `NHV_ReleaseOps.release_mark, `NHV_ReleaseOps.source])
    else if mode == "proof6" then
      (#[`NHV_COMBINED_IMPORT], #[`NHV_TailWindows.range_value, `NHV_TailWindows.stored_tail, `NHV_TailWindows.widths, `NHV_WindowFrame.adjacent, `NHV_WindowFrame.width, `NHV_WindowFrame.window_frame, `AspisR1.RPx_Deployed.deployed])
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

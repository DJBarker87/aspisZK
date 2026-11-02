import Lean
import R1Z.PV_RDCD5_NEPAudit
open Lean Elab Command
/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (_args : List String) : IO UInt32 := do
  enableInitializersExecution
  let mode := "v197"
  let modules := #[`R1Z.PV_RDCD5_V197ConsumerReplay]
  let roots := #[`R1Z.PV_RDCD4_SliceRange194.success,
    `R1Z.PV_RDCD4_SliceRange194.reversed,
    `R1Z.PV_RDCD4_SliceRange194.oversized,
    `R1Z.PV_RDCD4_SliceRange194.length,
    `R1Z.PV_RDCD4_SliceRange194.empty,
    `R1Z.PV_RDCD4_SliceRange194.full,
    `R1Z.PV_RDCD5_ParserRange.success,
    `R1Z.PV_RDCD5_ParserRange.oversized,
    `R1Z.PV_RDCD5_ParserRange.binding,
    `R1Z.PV_RDCD4_TryArray194.success,
    `R1Z.PV_RDCD4_TryArray194.mismatch,
    `R1Z.PV_RDCD4_TryArray194.backing,
    `R1Z.PV_RDCD4_TryArray194.roundtrip,
    `R1Z.PV_RDCD4_Endian194.binding,
    `R1Z.PV_RDCD4_BytesSource.scalar_binding,
    `R1Z.PV_RDCD4_ParserWindows.compose,
    `R1Z.PV_RDCD4_ParserWindows.component_window,
    `R1Z.PV_RDCD4_ParserWindows.no_write,
    `R1Z.PV_RDCD4_V197.source_reference,
    `R1Z.PV_RDCD4_V197.short_failure,
    `R1Z.PV_RDCD4_V197.frame,
    `R1Z.PV_RDCD4_V197.slice_instance,
    `R1Z.PV_RDCD5_ParserWindows.compose,
    `R1Z.PV_RDCD5_ParserWindows.component_window,
    `R1Z.PV_RDCD5_ParserWindows.no_write,
    `R1Z.PV_RDCD5_V197.source_reference,
    `R1Z.PV_RDCD5_V197.short_failure,
    `R1Z.PV_RDCD5_V197.frame,
    `R1Z.PV_RDCD5_V197.slice_instance,
    `R1Z.PV_RDCD5_ParserFlat.cm_window,
    `R1Z.PV_RDCD5_ParserTransport.bind_congr,
    `R1Z.PV_RDCD5_ParserTransport.range_bind,
    `R1Z.PV_RDCD5_ParserTransport.scalar,
    `R1Z.PV_RDCD5_ParserTransport.convert_component,
    `R1Z.PV_RDCD5_ParserTransport.component_binding,
    `R1Z.PV_RDCD5_ParserTransport.complex_shape,
    `R1Z.PV_RDCD5_ParserTransport.complex,
    `R1Z.PV_RDCD5_ParserTransport.quartic,
    `R1Z.PV_RDCD5_ParserErrors.existing_empty,
    `R1Z.PV_RDCD5_ParserErrors.owned_empty,
    `R1Z.PV_RDCD5_ParserErrors.carrier_agreement,
    `R1Z.PV_RDCD5_V197Restored.parser_instance,
    `R1Z.PV_RDCD5_V197Restored.window_instance,
    `R1Z.PV_RDCD5_V197Restored.input_frame,
    `R1Z.PV_RDCD5_V197Restored.rdcd4_instance,
    `R1Z.PV_RDCD5_V197ConsumerReplay.v197_corrected]
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

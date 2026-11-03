import Lean
import NER_Walker
open Lean Elab Command
unsafe def main (args : List String) : IO UInt32 := do
 enableInitializersExecution
 let selector := args.headD "sdk"
 let (mod, root) := if selector == "validator" then
   (`JFw_Validator, `AspisR1.JFw_Validator.loop_valid)
   else if selector == "record" then (`JFw_Record, `AspisR1.JFw_Record.success)
   else (`JGx_SdkAfterValidationEq, `AspisR1.JGx_SdkAfterValidationEq.source)
 let env ← importModules #[{module:=mod,importAll:=true}] {} (loadExts:=true) (level:=.private)
 let ctx : Command.Context := {fileName:="NER_FocusedDriver",fileMap:=FileMap.ofString "",snap?:=none,cancelTk?:=none}
 let action : CommandElabM Unit := do
  elabCommand (← `(command| #print axioms $(mkIdent root)))
  NEP.audit root ("NER_focused_" ++ selector)
 let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
 match result with
 | .error e => IO.eprintln (← e.toMessageData.toString); return 2
 | .ok (_, state) =>
  for msg in state.messages.toList do IO.println (← msg.data.toString)
  return if state.messages.hasErrors then 1 else 0

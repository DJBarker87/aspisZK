import Lean
import RPv_FJs_FinalMessage
import RPv_FJs_LiteralPair
import RPv_FJs_Finish
import RPv_FJs_OnRun
import RPv_FJs_GlobalPair
import RPv_FJv_GlobalOwners
import RPv_FJv_Finish
import RPv_FJv_Literal
import RPv_FJv_ActualLiteral
import RPv_FJv_Cont
import RPv_FJv_Caller
import RPv_FJv_Result
import RPv_FJv_Observations
import RPv_FJv_Top
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJs_FinalMessage, `RPv_FJs_LiteralPair, `RPv_FJs_Finish, `RPv_FJs_OnRun, `RPv_FJs_GlobalPair, `RPv_FJv_GlobalOwners, `RPv_FJv_Finish, `RPv_FJv_Literal, `RPv_FJv_ActualLiteral, `RPv_FJv_Cont, `RPv_FJv_Caller, `RPv_FJv_Result, `RPv_FJv_Observations, `RPv_FJv_Top ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPV_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPV_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPV_AUDIT_COMPLETE declarations={count} modules={selected.size}"

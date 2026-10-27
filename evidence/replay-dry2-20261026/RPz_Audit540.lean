import Lean
import R0P.Positivity
import R0P.Value
import R0P.Positive
import R0P.PositivityWired
import R0P.CopyConstants
import R0P.Copy
import R0P.PositivityChain
import R0P.Schedule

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R0P.Positivity, `R0P.Value, `R0P.Positive, `R0P.PositivityWired, `R0P.CopyConstants, `R0P.Copy, `R0P.PositivityChain, `R0P.Schedule ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let axs ← collectAxioms n
        logInfo m!"RPZ_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ_AUDIT_COMPLETE declarations={count} modules={selected.size}"

import Lean
import AspisR1RecordParser.Funs
import AspisR1PrefixAggregateParser.Funs
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisR1RecordParser.Funs, `AspisR1PrefixAggregateParser.Funs ]
  let mut rows : Array Json := #[]
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let value := c.value? true
        let refs := c.type.getUsedConstants ++ (value.map Expr.getUsedConstants |>.getD #[])
        let axs ← collectAxioms n
        rows := rows.push (Json.mkObj [
          ("module", toJson owner.toString), ("name", toJson n.toString),
          ("type", toJson (reprStr c.type)), ("value", toJson (reprStr value)),
          ("levelParams", toJson (reprStr c.levelParams)),
          ("hints", toJson (reprStr c.hints)), ("unsafe", toJson c.isUnsafe),
          ("axiom", toJson c.isAxiom), ("refs", toJson (refs.map Name.toString)),
          ("axioms", toJson (axs.map Name.toString))])
        elabCommand (← `(#print axioms $(mkIdent n)))
  liftIO <| IO.FS.writeFile "DFm_parser-before.json" (Json.arr rows).compress
  logInfo m!"DFM_AUDIT_COMPLETE declarations={rows.size}"

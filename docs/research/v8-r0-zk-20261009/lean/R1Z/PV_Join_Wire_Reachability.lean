import R1Z.PV_Join_Wire_Caller
import Lean
set_option autoImplicit false
namespace R1Z.PV_Join_Wire_Reachability
open Lean Elab Command
/-- Read-only declaration graph check: no theorem or trusted implementation. -/
elab "#wire_require " root:ident laws:str : command => do
  let env ← getEnv
  let mut todo := #[root.getId]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet.toArray do
          let text := dep.toString
          if text.startsWith "R1Z." || text.startsWith "_private.R1Z." then
            todo := todo.push dep
  let expected := laws.getString.splitOn ","
  for law in expected do
    unless seen.contains law.toName do
      throwError "WIRE MISSING: {law} from {root.getId}"
  logInfo m!"WIRE VERIFIED {expected.length} source laws in declaration closure of {root.getId}"
end R1Z.PV_Join_Wire_Reachability
#wire_require R1Z.PV_Join_Wire_Caller.refinement_of_data "R1Z.PV_CB_TakeSource.op3_source,R1Z.PV_CB_Op71Exact.op71_source,R1Z.PV_CB_Op72Exact.op72_source,R1Z.PV_CB_Op77Source.op77_source,R1Z.PV_CB_Op80Exact.op80_source,R1Z.PV_CB_Op82Source.op82_source,R1Z.PV_CB_Op83Source.op83_source,R1Z.PV_CB_Op84Exact.op84_source,R1Z.PV_CB_Op86Source.op86_source,R1Z.PV_CB_Op100Exact.op100_source,R1Z.PV_CB_Op101Exact.op101_source,R1Z.PV_CB_Op105Exact.op105_source,R1Z.PV_CB_Op107Exact.op107_source,R1Z.PV_CB_Op109Exact.op109_source,R1Z.PV_CB_Op110Source.op110_source,R1Z.PV_CB_Op111Source.op111_source,R1Z.PV_CB_Op114Source.op114_source,R1Z.PV_CB_Op118Exact.op118_source,R1Z.PV_CB3_Op120Source.op120_source,R1Z.PV_CB_Op127Source.op127_source,R1Z.PV_CB_Op128Source.op128_source,R1Z.PV_CB_Op130Source.op130_source,R1Z.PV_CB_Op131Source.op131_source,R1Z.PV_CB3_Op225Source.op225_source,R1Z.PV_CB_Op229Source.op229_source,R1Z.PV_CB3_Op246Source.op246_source,R1Z.PV_CB3_Op51Arbitrary.op51_source"

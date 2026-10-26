import Lean
import Rc7_Top
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  logInfo m!"RPZ4_COHERENT_GRAPH_COMPLETE modules={env.header.modules.size}"
#print axioms AspisR1.Rc7_Top.deployed

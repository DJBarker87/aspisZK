import Lean
import AspisR1BatchedAllPrefix
import BatchedWeightsActualReducer
import AspisR1BatchedWeightsValueActualV12
import AspisR1BatchedWeightsValueActualV19
import S8Kani2MutableValue
import S8Kani2SliceSet
import S8Kani2PrefixIndex
import S7OwnedP6LoopSimulation

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisR1BatchedAllPrefix, `BatchedWeightsActualReducer, `AspisR1BatchedWeightsValueActualV12, `AspisR1BatchedWeightsValueActualV19, `S8Kani2MutableValue, `S8Kani2SliceSet, `S8Kani2PrefixIndex, `S7OwnedP6LoopSimulation ]
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

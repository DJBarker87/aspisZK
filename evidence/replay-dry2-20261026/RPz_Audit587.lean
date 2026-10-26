import Lean
import S1M31EmbeddingSourceV1
import PaintBlocksPrefixV1
import S1NativeCompactTypesV1
import S1NativeCompactModelV1
import S1LoopSafetyV1
import S1NativeCompactFrameV1
import S1NativeCompactBodyFrameV1
import S1NativeCompactLoopFrameV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `S1M31EmbeddingSourceV1, `PaintBlocksPrefixV1, `S1NativeCompactTypesV1, `S1NativeCompactModelV1, `S1LoopSafetyV1, `S1NativeCompactFrameV1, `S1NativeCompactBodyFrameV1, `S1NativeCompactLoopFrameV1 ]
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

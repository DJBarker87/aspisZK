import Lean
import AllocationStageSpecM10
import ListConstructorAllocationM10
import BinNodeListWork
import BinMerkleRecoveryReads
import BinLeafBoundedTable
import ExtractorWorkMonad
import AllocationFoldM10
import PublicCursorAllocationM10

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AllocationStageSpecM10, `ListConstructorAllocationM10, `BinNodeListWork, `BinMerkleRecoveryReads, `BinLeafBoundedTable, `ExtractorWorkMonad, `AllocationFoldM10, `PublicCursorAllocationM10 ]
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

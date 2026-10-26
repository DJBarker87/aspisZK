import Lean
import R1MixedLeafDecoder
import AspisV8PairedCommitment.Table
import AspisV8R19.DuplexFrames
import AspisV8Privacy.FiniteGames
import AspisV8R17.AdaptiveOracle
import AspisV8R19.DuplexFreshPair
import AspisV8R19.SourceDuplexStep
import AspisV8R15.CircleChord

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1MixedLeafDecoder, `AspisV8PairedCommitment.Table, `AspisV8R19.DuplexFrames, `AspisV8Privacy.FiniteGames, `AspisV8R17.AdaptiveOracle, `AspisV8R19.DuplexFreshPair, `AspisV8R19.SourceDuplexStep, `AspisV8R15.CircleChord ]
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

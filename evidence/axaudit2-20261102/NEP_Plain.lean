import Lean
import NEP_Planted
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof, `NEP_Planted.viaAux] do
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut missing : Array String := #[]
    let mut axioms : Array String := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      if seen.contains n then continue
      seen := seen.insert n
      if let some c := env.checked.get.find? n then
        if c.isAxiom then axioms := axioms.push n.toString
        pending := pending ++ c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
      else missing := missing.push n.toString
    logInfo m!"NEP_PROBE {root}: missing={missing}, axioms={axioms}"
    logInfo m!"NEP_COLLECT {root}: {← collectAxioms root}"
#print axioms NEP_Planted.matcher
#print axioms NEP_Planted.viaPrivate
#print axioms NEP_Planted.proof
#print axioms NEP_Planted.viaAux

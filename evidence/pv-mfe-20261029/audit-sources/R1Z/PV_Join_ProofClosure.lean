import Lean
set_option autoImplicit false
namespace R1Z.PV_Join_ProofClosure
open Lean Elab Command
/-- Inspect R1Z/private-R1Z declaration type/value edges, never import membership.
External namespaces precede these source-law declarations in the import DAG.
This command adds no theorem, proof assumption or trusted implementation. -/
elab "#join_closure " root:ident : command => do
  let env ← getEnv
  let mut todo := #[root.getId]
  let mut seen : NameSet := {}
  let mut laws : Array Name := #[]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let text := name.toString
      if (text.startsWith "R1Z.PV_CB_" || text.startsWith "R1Z.PV_CB3_") && text.endsWith "_source" then
        laws := laws.push name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet.toArray do
          let text := dep.toString
          if text.startsWith "R1Z." || text.startsWith "_private.R1Z." then
            todo := todo.push dep
  logInfo m!"JOIN_CLOSURE {root.getId}: {laws.qsort Name.lt}"
end R1Z.PV_Join_ProofClosure

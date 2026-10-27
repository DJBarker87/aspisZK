import Lean
import RPz8_ARX_Root
open Lean Elab Command
#print Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.Formatter
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ARX_Root.deployed
run_cmd do
  let env := (← getEnv).setExporting false
  let target : Name := `Aeneas.Std.core.fmt.Formatter
  let some leaf := env.checked.get.find? target | throwError "missing Formatter"
  let kind := match leaf with
    | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque"
    | .defnInfo _ => "definition"
    | .inductInfo _ => "inductive"
    | _ => "other"
  logInfo m!"RPZ8_FORMATTER_KIND {(Json.mkObj [("kind", toJson kind), ("isAxiom", toJson leaf.isAxiom), ("type", toJson (repr leaf.type).pretty)]).compress}"
  let owner (n : Name) : String := match env.getModuleIdxFor? n with
    | some i => env.header.modules[i.toNat]!.module.toString
    | none => "current-or-builtin"
  for root in #[`AspisR1.Rc10_Top.deployed, `AspisR1.ARX_Root.deployed] do
    let mut pending : Array Name := #[root]
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut parents : NameMap (Name × String) := {}
    let mut axioms : Array Name := #[]
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      let some c := env.checked.get.find? n | throwError "missing checked constant {n}"
      if c.isAxiom then axioms := axioms.push n
      let values := ((c.value? true).map (fun e => e.getUsedConstants)).getD #[]
      let constructors := match c with
        | .inductInfo v => v.ctors.toArray
        | _ => #[]
      for (refs, edge) in #[(c.type.getUsedConstants, "type"), (values, "value"), (constructors, "inductive-constructor")] do
        for dep in refs do
          if !seen.contains dep then
            seen := seen.insert dep
            parents := parents.insert dep (n, edge)
            pending := pending.push dep
    let mut path : Array Name := #[target]
    let mut edges : Array String := #[]
    let mut current := target
    while current != root do
      let some (parent, edge) := parents.find? current | throwError "missing Formatter dependency parent {current}"
      path := path.push parent
      edges := edges.push edge
      current := parent
    path := path.reverse
    logInfo m!"RPZ8_FORMATTER_TRUST {(Json.mkObj [("root", toJson root.toString), ("reachable", toJson (seen.contains target)), ("path", toJson (path.map Name.toString)), ("owners", toJson (path.map owner)), ("edge_kinds", toJson edges.reverse), ("uncached_axiom_info_names", toJson (axioms.map Name.toString)), ("visited", toJson seen.toArray.size)]).compress}"
  logInfo "RPZ8_FORMATTER_TRUST_COMPLETE"

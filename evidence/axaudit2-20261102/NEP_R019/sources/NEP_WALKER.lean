import Lean
open Lean Elab Command
namespace NEP
/-- Raw checked-kernel graph. No imported axiom summaries enter the traversal. -/
def audit (root : Name) (stem : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut pending := #[(root, root)]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut axioms : Array String := #[]
  let mut edges := 0
  while !pending.isEmpty do
    let (n, parent) := pending.back!
    pending := pending.pop
    let some c := env.checked.get.find? n | do
      logInfo m!"NEP_FAILURE {(Json.mkObj [("root", toJson root.toString),
        ("missing", toJson n.toString), ("parent", toJson parent.toString),
        ("discovered_constants_before_failure", toJson seen.size),
        ("edges_scanned_before_failure", toJson edges),
        ("complete", toJson false)]).compress}"
      throwError "missing reachable constant {n}; parent {parent}; visited {seen.size}"
    if c.isAxiom then axioms := axioms.push n.toString
    let mut refs := c.type.getUsedConstants ++
      ((c.value? true).map Expr.getUsedConstants).getD #[]
    if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
    edges := edges + refs.size
    for dep in refs do
      if !seen.contains dep then
        seen := seen.insert dep
        pending := pending.push (dep, n)
  let reached := seen.toArray.qsort Name.lt
  liftIO <| IO.FS.writeFile (stem ++ "_REACHABLE.txt")
    (String.intercalate "\n" (reached.toList.map Name.toString) ++ "\n")
  let walked := axioms.qsort (· < ·)
  let reported := ((← collectAxioms root).map Name.toString).qsort (· < ·)
  logInfo m!"NEP_RESULT {(Json.mkObj [("root", toJson root.toString),
    ("reachable_constants", toJson reached.size), ("edges_scanned", toJson edges),
    ("walked_axioms", toJson walked), ("collect_axioms", toJson reported),
    ("equal", toJson (walked == reported))]).compress}"
  unless walked == reported do throwError "raw graph disagrees with collectAxioms"
/-- Reimport the requested closure with all private kernel data loaded.
Do not trust the caller's exported view or imported axiom summaries for traversal. -/
unsafe def auditModules (modules : Array Name) (roots : Array Name) (stem : String) : CommandElabM Unit := do
  let imports := modules.map fun n => ({ module := n, importAll := true } : Import)
  liftIO enableInitializersExecution
  let full ← liftIO <| importModules imports (← getOptions) (loadExts := true) (level := .private)
  withEnv full do
    for root in roots do
      elabCommand (← `(command| #print axioms $(mkIdent root)))
      audit root (stem ++ "_" ++ root.toString)
end NEP

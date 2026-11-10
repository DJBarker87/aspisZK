import Lean
/-! NPO_ read-only computability scoping (v2 of NPO_Noncomp; NPO_L024's list was unreliable because
imported extension entries were not loaded). Environment loaded with loadExts := true. Controls:
List.flatten, List.map (computable) and Classical.choose (noncomputable) are reported first.
For roots R: the noncomputable closure through values, and for every noncomputable constant its
cause class from its own value:
  classical  : value mentions Classical.choice/choose/propDecidable/indefiniteDescription/epsilon/dec*
  fixpoint   : value mentions Lean.Order.fix (partial_fixpoint, incl. Aeneas loops)
  opaque_ext : value mentions an opaque/axiom constant of non-Prop type, other than the above
  inherited  : none of the above; noncomputable only because a dependency is
Output NPO_NONCOMPUTABLE.json. -/
open Lean Meta
def classicalNames : List Name := [``Classical.choice, ``Classical.choose, ``Classical.propDecidable,
  ``Classical.indefiniteDescription, ``Classical.epsilon, `Classical.dec, `Classical.decEq,
  `Classical.decPred, `Classical.decRel, ``Classical.decidableInhabited, ``Classical.inhabited_of_nonempty]
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `NNH8_Exec}, {module := `NNH_Run6Installed}] {} (trustLevel := 1024) (loadExts := true)
  let ctl := [``List.flatten, ``List.map, ``Classical.choose].map fun n => (n.toString, isNoncomputable env n)
  IO.println s!"controls {ctl}"
  let roots := args.map String.toName
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots.toArray
  let mut rows : Array Json := #[]
  let mut counts : Std.HashMap String Nat := {}
  while h : stack.size > 0 do
    let n := stack.back; stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !isNoncomputable env n then continue
    let vs := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let ncDeps := vs.filter (isNoncomputable env)
    let cls := vs.filter (classicalNames.contains ·)
    let fix := vs.filter (· == ``Lean.Order.fix)
    let opq := vs.filter fun d => !classicalNames.contains d && match env.find? d with
      | some (.opaqueInfo _) | some (.axiomInfo _) => true | _ => false
    let cause := if !cls.isEmpty then "classical" else if !fix.isEmpty then "fixpoint"
      else if !opq.isEmpty then "opaque_ext" else if !ncDeps.isEmpty then "inherited" else "no_ir_other"
    counts := counts.insert cause (counts.getD cause 0 + 1)
    let modName := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).toString | none => "?"
    rows := rows.push (Json.mkObj [("n", toJson n.toString), ("module", toJson modName), ("kind", toJson (match ci with | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | _ => "other")),
      ("cause", toJson cause), ("classical", toJson (cls.map toString)), ("opaque", toJson (opq.map toString)),
      ("noncomputable_deps", toJson (ncDeps.map toString))])
    for d in ncDeps do stack := stack.push d
  let j := Json.mkObj [("roots", toJson args), ("controls", toJson (ctl.map fun (a,b) => Json.mkObj [("n", toJson a), ("noncomputable", toJson b)])),
    ("noncomputable_reached", toJson rows.size), ("by_cause", toJson (counts.toList.map fun (a,b) => Json.mkObj [("cause", toJson a), ("count", toJson b)])),
    ("constants", Json.arr rows)]
  IO.FS.writeFile "NPO_NONCOMPUTABLE.json" j.pretty
  IO.println s!"reached={rows.size} {counts.toList}"
  return 0

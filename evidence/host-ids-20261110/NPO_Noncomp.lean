import Lean
/-! NPO_ read-only: the noncomputable frontier under given roots. A frontier constant is one marked
noncomputable (Lean.isNoncomputable) none of whose value-dependencies is marked noncomputable;
these are the leaves a computable host instance would have to replace. Also lists axioms/opaques
reached through values. -/
open Lean
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `NNH8_Exec}, {module := `NNH_Run6Installed}] {} (trustLevel := 1024) (loadExts := false)
  let roots := args.map String.toName
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots.toArray
  let mut nc : Array Name := #[]
  let mut frontier : Array Json := #[]
  while h : stack.size > 0 do
    let n := stack.back; stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !isNoncomputable env n then continue
    nc := nc.push n
    let vs := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let ncDeps := vs.filter (isNoncomputable env)
    if ncDeps.isEmpty then
      let ax := vs.filter fun d => match env.find? d with | some (.axiomInfo _) | some (.opaqueInfo _) => true | _ => false
      let modName := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).toString | none => "?"
      frontier := frontier.push (Json.mkObj [("n", toJson n.toString), ("module", toJson modName),
        ("axioms_or_opaques_in_value", toJson (ax.map toString))])
    for d in ncDeps do stack := stack.push d
  let j := Json.mkObj [("roots", toJson args), ("noncomputable_reached", toJson nc.size), ("frontier", Json.arr frontier)]
  IO.FS.writeFile "NPO_NONCOMPUTABLE_FRONTIER.json" j.pretty
  IO.println s!"noncomputable_reached={nc.size} frontier={frontier.size}"
  return 0

import AspisFailureBoundModel
/-! Aspis port preparation (tool, nothing proved): the declaration-level dependency closure of the two Aspis model
theorems. Starting from every constant whose name ends in `failure_bound40P_model` or
`failure_le_per_query_model`, follow the constants used by each declaration (type and value) to a fixed point.
Output `top_closure.tsv`: defining module, constant, for every constant in the closure; `module_totals.tsv`:
module, number of constants it defines (all constants, including generated ones). -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let tops := env.constants.fold (init := (#[] : Array Name)) fun acc c _ =>
    let s := c.toString
    if s.endsWith "failure_bound40P_model" || s.endsWith "failure_le_per_query_model" then acc.push c else acc
  logInfo m!"tops {tops}"
  let mut seen : NameSet := {}
  let mut stack : List Name := tops.toList
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | c :: rest =>
      stack := rest
      if !seen.contains c then
        seen := seen.insert c
        match env.find? c with
        | some ci =>
          for u in ci.getUsedConstantsAsSet.toList do
            if !seen.contains u then stack := u :: stack
        | none => pure ()
  let mods := env.header.moduleNames
  let lines := seen.toList.filterMap fun c =>
    (env.getModuleIdxFor? c).map fun i => s!"{mods[i.toNat]!}\t{c}"
  IO.FS.writeFile "top_closure.tsv" (String.intercalate "\n" lines ++ "\n")
  let totals := env.constants.fold (init := (Std.HashMap.emptyWithCapacity 20000 : Std.HashMap Name Nat)) fun acc c _ =>
    match env.getModuleIdxFor? c with
    | some i => acc.insert mods[i.toNat]! (acc.getD mods[i.toNat]! 0 + 1)
    | none => acc
  IO.FS.writeFile "module_totals.tsv" (String.intercalate "\n" (totals.toList.map fun (m, n) => s!"{m}\t{n}") ++ "\n")
  logInfo m!"closure constants {seen.size}, lines {lines.length}"

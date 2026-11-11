import AspisFailureBoundModel

/-! Measurement only (proves nothing). Constant walk from the two model
theorems of `AspisFailureBoundModel` and from `final_decoding40`, copied from
`AspisJoinedMeasure` (the version that also visits the constructors and
recursors of every inductive type reached). It expands every constant whose
module is not a library module, so it is the full constant-dependency closure
inside the project, values of theorems included.

Input: `headline-iii.txt`, the modules classified two-transaction (class iii).
Output: `final-model-measure.tsv`, one line per (group, project module
reached, class), and two log lines per group. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let dir := "/home/dombarker/project-offloads/future-version-20261111/lean-src/"
  let txt ← IO.FS.readFile (dir ++ "headline-iii.txt")
  let iii : Std.HashSet String := txt.splitOn "\n" |>.filter (· ≠ "") |>.foldl (·.insert ·) {}
  let libs : List String := ["Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient"]
  let isLib (m : String) : Bool := libs.any (fun l => m == l || m.startsWith (l ++ "."))
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "_current"
  let groups : List (String × List Name) := [
    ("model_bound", [``AspisFailureBoundModel.failure_bound40P_model]),
    ("model_per_query", [``AspisFailureBoundModel.failure_le_per_query_model]),
    ("final_decoding40", [``AspisFailureBoundModel.final_decoding40]),
    ("both", [``AspisFailureBoundModel.failure_bound40P_model,
       ``AspisFailureBoundModel.failure_le_per_query_model])]
  let mut lines : Array String := #[]
  for (g, roots) in groups do
    let mut seen : Std.HashSet Name := {}
    let mut stack := roots
    let mut mods : Std.HashSet String := {}
    let mut libConsts := 0
    while !stack.isEmpty do
      let c := stack.head!
      stack := stack.tail!
      if seen.contains c then continue
      seen := seen.insert c
      let m := modOf c
      if isLib m then
        libConsts := libConsts + 1
      else
        mods := mods.insert m
        match env.find? c with
        | some ci =>
          stack := ci.getUsedConstantsAsSet.toList ++ stack
          -- A structure or inductive type: visit its constructors and recursor too, so that
          -- constants occurring only in field types are reached even when no constructor is used.
          match ci with
          | .inductInfo v =>
            stack := v.ctors ++ stack
            stack := (Name.mkStr c "rec") :: stack
            stack := v.all ++ stack
          | .ctorInfo v => stack := v.induct :: stack
          | .recInfo v => stack := v.all ++ stack
          | _ => pure ()
        | none => pure ()
    let hit := mods.toList.filter iii.contains
    for m in mods.toList do
      lines := lines.push s!"{g}\t{m}\t{if iii.contains m then "iii" else "-"}"
    logInfo s!"{g}: {mods.size} project modules, {seen.size - libConsts} project constants, {libConsts} library constants at the boundary, class iii modules reached: {hit.length} {hit}"
    -- The one declaration in the Aspis files that raises an option
    -- (`exponentiation.threshold 600`): is it in this closure?
    logInfo s!"{g}: uses AspisFuture.StageD.perKind_margin: {seen.contains `AspisFuture.StageD.perKind_margin}"
  -- The import closure of this file, for comparison with the constant closure.
  let imported := env.header.moduleNames.toList.map (·.toString)
  let importedProject := imported.filter (fun m => !isLib m)
  let importedIii := importedProject.filter iii.contains
  logInfo s!"import closure: {imported.length} modules, {importedProject.length} project modules, class iii imported: {importedIii.length} {importedIii}"
  IO.FS.writeFile (dir ++ "final-model-measure.tsv") (String.intercalate "\n" lines.toList)

import AspisChargedHitMass40
import AspisCharge40

/-! Measurement only (proves nothing). Asked for by the reviewer of
80e6a852d13: the earlier constant walks (PSD-32, PSD-34) were rooted at
`hit_mass`, `starts` and `verifier_starts`, not at the composed bound.

This walk is rooted at the composed bound itself and at the two lemmas the
reviewer named. Unlike the earlier walks it does not use an expansion list:
it expands every constant whose module is not a library module (Mathlib,
Lean core, Std, Batteries and the other packages listed below), so it is the
full constant-dependency closure inside the project. Constants used in a
proof term are included, because `getUsedConstantsAsSet` reads the value of
a theorem as well as its type.

Input: `headline-iii.txt`, the modules classified two-transaction (class iii)
in `aspis-instance-module-classes.tsv`.
Output: `headline-measure.tsv`, one line per (group, project module reached,
class), and two log lines per group. The second log line says whether the
closure contains `perKind_margin`, the one declaration in the Aspis files
that raises an option (`exponentiation.threshold 600`). -/
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
    ("headline", [``AspisPerStep.ChargedHitMass40.restricted_union_bound_weighted40]),
    ("decFinal_le_charge40", [``AspisCharge40.decFinal_le_charge40]),
    ("charged_weight40", [``AspisPerStep.ChargedWeight40.charged_weight40]),
    ("all_three", [``AspisPerStep.ChargedHitMass40.restricted_union_bound_weighted40,
       ``AspisCharge40.decFinal_le_charge40, ``AspisPerStep.ChargedWeight40.charged_weight40])]
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
        | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
        | none => pure ()
    let hit := mods.toList.filter iii.contains
    for m in mods.toList do
      lines := lines.push s!"{g}\t{m}\t{if iii.contains m then "iii" else "-"}"
    logInfo s!"{g}: {mods.size} project modules, {seen.size - libConsts} project constants, {libConsts} library constants at the boundary, class iii modules reached: {hit.length} {hit}"
    -- The one declaration in the Aspis files that raises an option
    -- (`exponentiation.threshold 600`): is it in this closure?
    logInfo s!"{g}: uses AspisFuture.StageD.perKind_margin: {seen.contains ``AspisFuture.StageD.perKind_margin}"
  -- The import closure of this file, for comparison with the constant closure.
  let imported := env.header.moduleNames.toList.map (·.toString)
  let importedProject := imported.filter (fun m => !isLib m)
  let importedIii := importedProject.filter iii.contains
  logInfo s!"import closure: {imported.length} modules, {importedProject.length} project modules, class iii imported: {importedIii.length} {importedIii}"
  IO.FS.writeFile (dir ++ "headline-measure.tsv") (String.intercalate "\n" lines.toList)

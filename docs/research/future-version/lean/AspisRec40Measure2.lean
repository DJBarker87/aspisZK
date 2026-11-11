import AspisRec40HitMass

/-! Measurement only (proves nothing): modules whose constants the Aspis
start count and hit-mass equality use, expanded through the changed-dependent
and two-transaction modules (measure-expand.txt) and every Aspis module. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure-expand.txt"
  let expand : Std.HashSet String := txt.splitOn "\n" |>.filter (· ≠ "") |>.foldl (·.insert ·) {}
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "_current"
  let roots := [``AspisRec40.HitMass.hit_mass, ``AspisRec40.HitMass.mass_of_recovered,
    ``AspisRec40.ChargePrefix.starts, ``AspisRows40.FinalStarts.verifier_starts]
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  let mut mods : Std.HashSet String := {}
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let m := modOf c
    mods := mods.insert m
    if expand.contains m || m.startsWith "Aspis" then
      match env.find? c with
      | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
      | none => pure ()
  IO.FS.writeFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure2-mods.txt"
    (String.intercalate "\n" mods.toList)
  logInfo s!"{mods.size} modules, {seen.size} constants"

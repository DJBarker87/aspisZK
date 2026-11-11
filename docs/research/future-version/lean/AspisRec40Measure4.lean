import Frozen2StartChargeProbability

/-! Measurement only (proves nothing): constant-dependency walk of R1's clean
event (`Frozen2StartChargeClean.clean`) and of `failure_bound`, expanded through
the changed-dependent and two-transaction modules (measure-expand.txt); writes
each reached constant with its module. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure-expand.txt"
  let expand : Std.HashSet String := txt.splitOn "\n" |>.filter (· ≠ "") |>.foldl (·.insert ·) {}
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "_current"
  for (g, roots) in [("clean", [``AspisR1.Frozen2StartChargeClean.clean]),
      ("failure", [``AspisR1.Frozen2StartChargeProbability.failure_bound])] do
    let mut seen : Std.HashSet Name := {}
    let mut stack := roots
    let mut lines : Array String := #[]
    while !stack.isEmpty do
      let c := stack.head!
      stack := stack.tail!
      if seen.contains c then continue
      seen := seen.insert c
      let m := modOf c
      if expand.contains m then
        lines := lines.push s!"{m}\t{c}"
        match env.find? c with
        | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
        | none => pure ()
    IO.FS.writeFile s!"/home/dombarker/project-offloads/future-version-20261111/lean-src/measure4-{g}.tsv"
      (String.intercalate "\n" lines.toList)
    logInfo s!"{g}: {lines.size} expanded constants"

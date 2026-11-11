import Frozen2StartChargeProbability
import DecoderQueryAccounting
import RawFullPublicSelection

/-! Measurement only (proves nothing): the constant-dependency closure of the
charged-experiment roots, expanded through the modules that depend on a
replaced definition (list read from expand.txt), reported per module. -/
open Lean Elab Command

def rootGroups : List (String × List Name) := [
  ("charged", [``AspisR1.Frozen2StartChargePrefix.charged, ``AspisR1.Frozen2StartChargePrefix.charged_eval,
     ``AspisR1.Frozen2StartChargePrefix.prover_eval, ``AspisR1.Frozen2StartChargePrefix.base]),
  ("starts", [``AspisR1.Frozen2StartChargePrefix.starts, ``AspisR1.DecoderQueryAccounting.starts_le_queries,
     ``AspisR1.RecordedBinaryExperimentBin.dec]),
  ("clean", [``AspisR1.Frozen2StartChargeClean.clean, ``AspisR1.Frozen2StartChargeClean.bad,
     ``AspisR1.Frozen2StartChargeClean.prefixHit]),
  ("hitmass", [``AspisR1.Frozen2StartChargeProbability.hit_mass,
     ``AspisR1.Frozen2StartChargeProbability.restricted_union_bound]),
  ("failure", [``AspisR1.Frozen2StartChargeProbability.failure_bound]),
  ("honestsel", [``AspisR1.RawFullPublicSelection.bounded_at_first_cell])]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure-expand.txt"
  let expand : Std.HashSet String := txt.splitOn "\n" |>.filter (· ≠ "") |>.foldl (·.insert ·) {}
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "_current"
  for (g, roots) in rootGroups do
    let mut seen : Std.HashSet Name := {}
    let mut stack := roots
    let mut counts : Std.HashMap String Nat := {}
    while !stack.isEmpty do
      let c := stack.head!
      stack := stack.tail!
      if seen.contains c then continue
      seen := seen.insert c
      let m := modOf c
      counts := counts.insert m (counts.getD m 0 + 1)
      if expand.contains m then
        match env.find? c with
        | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
        | none => pure ()
    let mut lines : Array String := #[]
    for (m, k) in counts.toList do
      lines := lines.push s!"{g}\t{m}\t{k}\t{if expand.contains m then "expanded" else "leaf"}"
    IO.FS.writeFile s!"/home/dombarker/project-offloads/future-version-20261111/lean-src/measure-{g}.tsv" (String.intercalate "\n" lines.toList)
    logInfo s!"{g}: {counts.size} modules, {seen.size} constants"

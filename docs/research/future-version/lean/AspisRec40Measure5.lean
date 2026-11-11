import Frozen2StartChargeProbability

/-! Measurement only (proves nothing): per-component constant closures of the
pieces R1's clean event (`Frozen2StartChargeClean.clean`) is assembled from,
expanded through the changed-dependent and two-transaction modules. -/
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure-expand.txt"
  let expand : Std.HashSet String := txt.splitOn "\n" |>.filter (· ≠ "") |>.foldl (·.insert ·) {}
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "_current"
  let groups : List (String × List Name) := [
    ("H_defs", [``AspisR1.RawRecordedOracleExtractionMassBin.CleanAcceptedModel,
       ``AspisR1.Frozen2StartChargeClean.bad, ``AspisR1.OraclePortFrozen2Consumer.projected]),
    ("E_prefix", [``AspisR1.Frozen2StartChargePrefix.same_transcript,
       ``AspisR1.Frozen2StartChargePrefix.chronological_prefix,
       ``AspisR1.Frozen2StartChargePrefix.recovered_eval,
       ``AspisR1.OraclePortFrozen2Probability.first_reads]),
    ("D_format", [``AspisR1.RWireCheckedFormat.format_of_checks, ``AspisR1.RWireCheckedFormat.format_of_enrich]),
    ("C_tag", [``AspisR1.OraclePortAdmission.accepted_tag, ``AspisR1.OraclePortFrozen2Consumer.admitted_dV]),
    ("B_words", [``AspisR1.OraclePortCleanModel.extractor_word_alignment]),
    ("G_hit", [``AspisR1.Frozen2StartChargeCompletion.hit_in_prefix]),
    ("F_decodes", [``AspisR1.Frozen2StartChargeCompletion.decodes]),
    ("A_checks", [``AspisR1.OraclePortFrozen2Consumer.fibre_checks])]
  let mut lines : Array String := #[]
  for (g, roots) in groups do
    let mut seen : Std.HashSet Name := {}
    let mut stack := roots
    let mut mods : Std.HashSet String := {}
    while !stack.isEmpty do
      let c := stack.head!
      stack := stack.tail!
      if seen.contains c then continue
      seen := seen.insert c
      let m := modOf c
      if expand.contains m then
        mods := mods.insert m
        match env.find? c with
        | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
        | none => pure ()
    for m in mods.toList do lines := lines.push s!"{g}\t{m}"
  IO.FS.writeFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/measure5.tsv"
    (String.intercalate "\n" lines.toList)
  logInfo s!"{lines.size} rows"

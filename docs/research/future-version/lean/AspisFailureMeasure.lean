import Frozen2StartChargeProbability
import QueryScanModelFailure

/-! Measurement only (proves nothing): constant-dependency closures of the
pieces of R1's failure bound that the Aspis assembly (AspisFailureBound)
leaves as named hypotheses or reuses, expanded through the modules that
depend on a replaced definition or are two-transaction modules
(`measure-expand.txt`, the rows agent's list); every other module is a leaf
(reused unchanged). Method of `AspisRec40Measure`. Output: one line per
(group, expanded module) in `psa-failure-measure.tsv`. -/
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
    ("gap1_checks", [``AspisR1.OraclePortFrozen2Consumer.fibre_checks]),
    ("gap1_tag", [``AspisR1.OraclePortAdmission.accepted_tag, ``AspisR1.OraclePortFrozen2Consumer.admitted_dV]),
    ("gap1b_words", [``AspisR1.OraclePortCleanModel.extractor_word_alignment]),
    ("gap2_hit", [``AspisR1.Frozen2StartChargeCompletion.decodes,
       ``AspisR1.Frozen2StartChargeCompletion.hit_in_prefix,
       ``AspisR1.RWireCheckedFormat.format_of_checks, ``AspisR1.RWireCheckedFormat.format_of_enrich,
       ``AspisR1.Frozen2StartChargePrefix.same_transcript,
       ``AspisR1.Frozen2StartChargePrefix.chronological_prefix]),
    ("abort", [``AspisR1.RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_hit_add_abort,
       ``AspisR1.RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_supplied_hit_bound,
       ``AspisR1.RawRecordedOracleExtractionMassBin.CleanAcceptedModel,
       ``AspisR1.RawRecordedOracleExtractionMassBin.failureMass]),
    ("scan", [``AspisR1.QueryScanModelFailure.exhaustion_bound,
       ``AspisR1.QueryScanModelFailure.failureProbability]),
    ("collision", [``AspisR1.BinCombinedMerkleCollision.mass, ``AspisR1.BinCombinedMerkleCollision.kappa])]
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
    logInfo s!"{g}: {mods.size} expanded modules, {seen.size} constants"
  IO.FS.writeFile "/home/dombarker/project-offloads/future-version-20261111/lean-src/psa-failure-measure.tsv"
    (String.intercalate "\n" lines.toList)

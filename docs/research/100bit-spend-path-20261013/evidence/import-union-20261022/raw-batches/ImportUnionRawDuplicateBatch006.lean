import Lean
open Lean
private def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "Empty module")
  pure data

#eval show IO Unit from do
  let requests : Array (String × Array (String × String)) := #[("algHomEquivSigma.eq_1", #[("Mathlib.RingTheory.Trace.Basic", "theorem"), ("Mathlib.RingTheory.Norm.Basic", "theorem")]),
("cast.congr_simp", #[("Init.Data.Fin.Lemmas", "theorem"), ("Init.Data.Fin.Iterate", "theorem"), ("Init.Data.Iterators.Basic", "theorem"), ("Std.Data.DTreeMap.Internal.Operations", "theorem"), ("Std.Data.Internal.List.Associative", "theorem")]),
("dite.congr_simp", #[("Init.GetElem", "theorem"), ("Init.Data.Nat.Div.Basic", "theorem"), ("Init.Data.Nat.Sqrt.Basic", "theorem")]),
("eq_self_iff_true._simp_1", #[("Mathlib.Logic.Equiv.PartialEquiv", "theorem"), ("Mathlib.Tactic.ReduceModChar", "theorem")]),
("forall_const._simp_2", #[("Mathlib.Tactic.Attr.Core", "theorem"), ("Mathlib.Tactic.Push", "theorem"), ("Aeneas.Tactic.Simp.SimpBoolProp.SimpBoolProp", "theorem")]),
("ge_iff_le._simp_2", #[("Aeneas.Tactic.Simp.SimpScalar.SimpScalar", "theorem"), ("Aeneas.Tactic.Conv.ZModify.ZModify", "theorem")]),
("getModify.eq_1", #[("Std.Do.Triple.SpecLemmas", "theorem"), ("Batteries.Control.LawfulMonadState", "theorem")]),
("gt_iff_lt._simp_2", #[("Aeneas.Tactic.Solver.ScalarTac.Lemmas", "theorem"), ("Aeneas.Tactic.Simp.SimpScalar.SimpScalar", "theorem"), ("Aeneas.Tactic.Conv.ZModify.ZModify", "theorem")]),
("guard.eq_1", #[("Mathlib.Data.Option.Basic", "theorem"), ("Mathlib.Control.Basic", "theorem")]),
("ite.congr_simp", #[("Init.Data.NeZero", "theorem"), ("Init.ByCases", "theorem")]),
("modify.eq_1", #[("Std.Do.Triple.SpecLemmas", "theorem"), ("Batteries.Control.LawfulMonadState", "theorem")]),
("nhdsKer.eq_1", #[("Mathlib.Topology.Separation.Regular", "theorem"), ("Mathlib.Topology.NhdsKer", "theorem")]),
("not_or._simp_2", #[("Mathlib.Tactic.Push", "theorem"), ("Aeneas.Tactic.Simp.SimpBoolProp.SimpBoolProp", "theorem")]),
("toContinuousMap.congr_simp", #[("Mathlib.Topology.Sets.Opens", "theorem"), ("Mathlib.Topology.ContinuousMap.Star", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-006.jsonl" .write
  let mut types : Std.HashMap String Expr := {}
  let mut equal : Std.HashMap String Bool := {}
  let mut found : Std.HashMap String (Array String) := {}
  let owners := requests.foldl (fun acc (_, os) => os.foldl (fun a (o, _) => if a.contains o then a else a.push o) acc) (#[] : Array String)
  for owner in owners do
    let wanted := requests.filter (fun (_, os) => os.any (fun (o, _) => o == owner))
    let mut file : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        file := some p
        break
    let some p := file | throw (IO.userError s!"Missing {owner}")
    let data ← readComplete p
    for ci in data.constants do
      let name := ci.name.toString
      if wanted.any (fun (n, _) => n == name) then
        found := found.insert name ((found[name]?.getD #[]).push owner)
        if let some old := types[name]? then
          equal := equal.insert name ((equal[name]?.getD true) && old == ci.type)
        else
          types := types.insert name ci.type
        out.putStrLn ("RAW_DUP_TYPE " ++ (Json.arr #[toJson name, toJson owner, toJson ((hash ci.type).toNat)]).compress)
  for (name, os) in requests do
    let actual := found[name]?.getD #[]
    unless actual.size == os.size && os.all (fun (o, _) => actual.contains o) do
      throw (IO.userError s!"Missing duplicate owner for {name}")
    let sameType := equal[name]?.getD true
    let allowed := os.all (fun (_, k) => k == "theorem") && sameType
    out.putStrLn ("RAW_DUP " ++ (Json.arr #[toJson name, toJson os, toJson sameType, toJson allowed]).compress)
  out.flush
  IO.println ("RAW_BATCH_COMPLETE " ++ toString requests.size)

import Lean
/-! NPO_ statement reader (read-only; adds no declaration). For each run-7 root R and instance I:
 (1) reverse check: renaming NPO_<I>.X back to X and the three NPO ids back to the original id
     constants turns the clone's kernel type into TAS_FinalB's kernel type exactly (Expr equality);
 (2) lists the constants that occur in the clone's type but not in the original's (the diff);
 (3) Lean.collectAxioms of the clone root;
 (4) pp.all kernel statements of the original and the clone, written to files. -/
open Lean Meta
namespace NPO_Stmt
def roots : List Name := [`AspisR1.TAS_FinalB.deployed_splitB, `AspisR1.TAS_FinalB.deployed_charge,
  `AspisR1.TAS_FinalB.fail_sub_rec, `AspisR1.NNH8_DeployedOuter]
def back (inst : String) (n : Name) : Name :=
  let pre := Name.mkSimple s!"NPO_{inst}"
  if n == Name.mkStr `NPO_DeployedIds s!"verifier{inst}" then `AspisR1.CPH_Program.verifier
  else if n == Name.mkStr `NPO_DeployedIds s!"pool{inst}" then `NHJ_IdPacket.poolDefault
  else if n == Name.mkStr `NPO_DeployedIds s!"registry{inst}" then `NHJ_IdPacket.registryDefault
  else if pre.isPrefixOf n then n.replacePrefix pre .anonymous else n
partial def unsub (inst : String) (e : Expr) : Expr := e.replace fun x => match x with
  | .const n us => some (.const (back inst n) us)
  | .proj s i b => some (.proj (back inst s) i (unsub inst b))
  | _ => none
def run (inst : String) : MetaM Json := do
  let env ← getEnv
  let mut out : Array Json := #[]
  for r in roots do
    let pre := Name.mkSimple s!"NPO_{inst}"
    let some o := env.find? r | throwError "missing {r}"
    let some c := env.find? (pre ++ r) | throwError "missing clone {r}"
    let same := unsub inst c.type == o.type
    let oc := o.type.getUsedConstants.toList
    let added := c.type.getUsedConstants.toList.filter (fun n => !oc.contains n) |>.map toString
    let removed := oc.filter (fun n => !c.type.getUsedConstants.contains n) |>.map toString
    let ax ← collectAxioms (pre ++ r)
    let ppo ← withOptions (fun o => (o.setBool `pp.all true).setBool `pp.proofs false) (ppExpr o.type)
    let ppc ← withOptions (fun o => (o.setBool `pp.all true).setBool `pp.proofs false) (ppExpr c.type)
    IO.FS.writeFile s!"NPO_STMT_{inst}_{r.toString}.orig.txt" s!"{ppo}\n"
    IO.FS.writeFile s!"NPO_STMT_{inst}_{r.toString}.clone.txt" s!"{ppc}\n"
    out := out.push <| Json.mkObj [("root", toJson r.toString), ("clone", toJson (pre ++ r).toString),
      ("reverse_renaming_gives_original_type", toJson same), ("constants_only_in_clone_type", toJson added),
      ("constants_only_in_original_type", toJson removed),
      ("axioms", toJson (ax.map toString))]
  return Json.arr out
end NPO_Stmt
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `NPO_CloneNov}, {module := `NPO_CloneOct}] {} (trustLevel := 1024) (loadExts := false)
  let mut res : Array Json := #[]
  for inst in args do
    let ctx : Core.Context := { fileName := "<NPO_Stmt>", fileMap := default, maxHeartbeats := 0 }
    let (j, _) ← ((NPO_Stmt.run inst).run' {} {}).toIO ctx { env }
    res := res.push (Json.mkObj [("instance", toJson inst), ("roots", j)])
  IO.FS.writeFile "NPO_STATEMENTS.json" (Json.arr res).pretty
  IO.println (Json.arr res).compress
  return 0

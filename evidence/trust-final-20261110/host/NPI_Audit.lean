import TAS_FinalB
import Lean
/-! NPI_ trust and axiom audit of the replayed TAS_FinalB closure (read-only census, no theorem).
Revision 2: v1 traversed every constant's value (getUsedConstantsAsSet over 882k constants) and was stopped by
-M7000 at 7.2 GB RSS (attempt NPI_L003). This revision reads only constant headers (kind, name, module): no value
or type is traversed. Users of trust carriers are taken from source text instead.
Inputs: NPI_cone_union.txt (deployed_splitB ∪ deployed_charge raw ax2 cones, L187 final), NPI_targets.txt,
NPI_roots.txt (ledger30 row roots and RT item roots). -/
open Lean

def npiDir : System.FilePath := "/home/dombarker/project-offloads/codex-cx-trust-20261110/run"

def readSet (f : String) : IO (Std.HashSet String) := do
  let ls ← IO.FS.lines (npiDir / f)
  return ls.foldl (fun s l => if l.trim.isEmpty then s else s.insert l.trim) {}

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => match env.header.moduleNames[i.toNat]? with
    | some m => m.toString false
    | none => "?"
  | none => "<current>"

def census (env : Environment) (cone : Std.HashSet String) : Nat × Nat × Array (Name × Bool × Bool) :=
  env.constants.fold (fun (acc : Nat × Nat × Array (Name × Bool × Bool)) n ci =>
    let (c, k, a) := acc
    let inCone := cone.contains (n.toString false)
    let k := if inCone then k + 1 else k
    match ci with
    | .axiomInfo v => (c + 1, k, a.push (n, inCone, v.isUnsafe))
    | _ => (c + 1, k, a)) (0, 0, #[])

run_meta do
  let env ← getEnv
  let cone ← readSet "NPI_cone_union.txt"
  let targets ← readSet "NPI_targets.txt"
  let roots ← IO.FS.lines (npiDir / "NPI_roots.txt")
  let std : List String := ["propext", "Classical.choice", "Quot.sound"]
  let (nConst, nCone, axs) := census env cone
  let axl := axs.map fun (n, inCone, uns) =>
    let s := n.toString false
    s!"{s}\t{modOf env n}\t{if std.contains s then "STANDARD" else "NONSTANDARD"}\t{inCone}\t{uns}"
  let mut rl : Array String := #[]
  for r in roots do
    let r := r.trim
    if r.isEmpty then continue
    let n1 := r.toName
    let n2 := (`AspisR1).append r.toName
    let e1 := env.contains n1
    let e2 := env.contains n2
    let c1 := cone.contains r
    let c2 := cone.contains ("AspisR1." ++ r)
    let m := if e1 then modOf env n1 else if e2 then modOf env n2 else "-"
    rl := rl.push s!"{r}\t{e1 || e2}\t{c1 || c2}\t{m}"
  let mut tl : Array String := #[]
  for t in targets.toList do
    tl := tl.push s!"{t}\t{env.contains t.toName}\t{cone.contains t}\t{modOf env t.toName}"
  IO.FS.writeFile (npiDir / "NPI_out_axioms.tsv") ("\n".intercalate axl.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_roots.tsv") ("\n".intercalate rl.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_targets.tsv") ("\n".intercalate tl.toList ++ "\n")
  let summ := s!"constants={nConst}\ncone_matched={nCone}\ncone_list={cone.size}\naxioms={axs.size}\nroots={rl.size}\nmodules={env.header.moduleNames.size}\n"
  IO.FS.writeFile (npiDir / "NPI_out_summary.txt") summ
  logInfo summ


import Lean
/-! NPI_ trust and axiom audit of the replayed TAS_FinalB closure (read-only census, no theorem).
Inputs (workspace files): NPI_cone_union.txt (deployed_splitB ∪ deployed_charge raw ax2 cones, L187 final),
NPI_targets.txt (trust carrier constants), NPI_roots.txt (ledger30 row roots and RT item roots).
Outputs: NPI_out_axioms.tsv, NPI_out_sorry.tsv, NPI_out_users.tsv, NPI_out_roots.tsv, NPI_out_summary.txt. -/
open Lean

def npiDir : System.FilePath := "/home/dombarker/project-offloads/codex-cx-trust-20261110/test"

def readSet (f : String) : IO (Std.HashSet String) := do
  let ls ← IO.FS.lines (npiDir / f)
  return ls.foldl (fun s l => if l.trim.isEmpty then s else s.insert l.trim) {}

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => match env.header.moduleNames[i.toNat]? with
    | some m => m.toString false
    | none => "?"
  | none => "<current>"

run_meta do
  let env ← getEnv
  let cone ← readSet "NPI_cone_union.txt"
  let targets ← readSet "NPI_targets.txt"
  let roots ← IO.FS.lines (npiDir / "NPI_roots.txt")
  let std : List String := ["propext", "Classical.choice", "Quot.sound"]
  let mut axl : Array String := #[]
  let mut sorryUsers : Array String := #[]
  let mut users : Array String := #[]
  let mut nConst := 0
  let mut nCone := 0
  let mut nAx := 0
  for (n, ci) in env.constants.toList do
    nConst := nConst + 1
    let s := n.toString false
    let inCone := cone.contains s
    if inCone then nCone := nCone + 1
    match ci with
    | .axiomInfo v =>
        nAx := nAx + 1
        let kind := if std.contains s then "STANDARD" else "NONSTANDARD"
        axl := axl.push s!"{s}\t{modOf env n}\t{kind}\t{inCone}\t{v.isUnsafe}"
    | _ => pure ()
    let used : NameSet := ci.getUsedConstantsAsSet
    if used.contains ``sorryAx then
      sorryUsers := sorryUsers.push s!"{s}\t{modOf env n}\t{inCone}"
    if inCone then
      for u in used do
        let us := u.toString false
        if targets.contains us then
          users := users.push s!"{us}\t{s}\t{modOf env n}"
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
    tl := tl.push s!"{t}\t{env.contains t.toName}\t{cone.contains t}"
  IO.FS.writeFile (npiDir / "NPI_out_axioms.tsv") ("\n".intercalate axl.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_sorry.tsv") ("\n".intercalate sorryUsers.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_users.tsv") ("\n".intercalate users.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_roots.tsv") ("\n".intercalate rl.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_out_targets.tsv") ("\n".intercalate tl.toList ++ "\n")
  let summ := s!"constants={nConst}\ncone_matched={nCone}\ncone_list={cone.size}\naxioms={nAx}\nsorry_users={sorryUsers.size}\nuser_edges={users.size}\nroots={rl.size}\nmodules={env.header.moduleNames.size}\n"
  IO.FS.writeFile (npiDir / "NPI_out_summary.txt") summ
  logInfo summ

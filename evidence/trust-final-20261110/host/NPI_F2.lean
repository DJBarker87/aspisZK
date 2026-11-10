import TAS_FinalB
import Lean
/-! NPI_ F2: do the certificates of the 28 NOT-IN-CONE reviewed-transcription entries feed a model in the cones?
Header- and type-only (no value traversal; NPI_L003 lesson). For each certificate constant: existence, cone
membership, module, and the constants of its STATEMENT (type only) that lie in both cones. For each certificate
module: number of its declarations and how many of them lie in the cones. -/
open Lean

def npiDir : System.FilePath := "/home/dombarker/project-offloads/codex-cx-trust-20261110/f2"

def readSet (f : String) : IO (Std.HashSet String) := do
  let ls ← IO.FS.lines (npiDir / f)
  return ls.foldl (fun s l => if l.trim.isEmpty then s else s.insert l.trim) {}

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => match env.header.moduleNames[i.toNat]? with
    | some m => m.toString false
    | none => "?"
  | none => "<current>"

def boring (s : String) : Bool :=
  ["Init.", "Lean.", "Mathlib.", "Std.", "Aeneas.", "Nat.", "List.", "Option.", "Prod.", "Eq", "And", "Or", "Iff",
   "Bool", "Array.", "Fin.", "BitVec", "UInt", "Int.", "Exists", "Not", "True", "False", "HEq", "Decidable", "instDecidable",
   "instOfNat", "OfNat", "HAdd", "HSub", "HMul", "LT.", "LE.", "GT.", "GE.", "Membership", "Subtype", "Sigma", "PUnit", "Unit"].any
    (fun p => s.startsWith p) || s == "Eq" || s == "Nat" || s == "List" || s == "Option" || s == "Prod"

def census (env : Environment) (cone : Std.HashSet String) (mods : Std.HashSet String) :
    Std.HashMap String (Nat × Nat × Array String) :=
  env.constants.fold (fun (acc : Std.HashMap String (Nat × Nat × Array String)) n _ =>
    let m := modOf env n
    if mods.contains m then
      let s := n.toString false
      let (t, c, a) := acc.getD m (0, 0, #[])
      let inC := cone.contains s
      acc.insert m (t + 1, if inC then c + 1 else c, if inC && a.size < 12 then a.push s else a)
    else acc) {}

run_meta do
  let env ← getEnv
  let cone ← readSet "NPI_cone_union.txt"
  let mods ← readSet "f2_modules.txt"
  let names ← IO.FS.lines (npiDir / "f2_names.tsv")
  let mut out : Array String := #[]
  for l in names do
    let p := l.trim.splitOn "\t"
    if p.length < 2 then continue
    let item := p[0]!
    let r := p[1]!
    let cand := [r.toName, (`AspisR1).append r.toName]
    match cand.find? (env.contains ·) with
    | none => out := out.push s!"{item}\t{r}\tMISSING\t-\t-\t-"
    | some n =>
      let ci := env.find? n |>.get!
      let s := n.toString false
      let ts : NameSet := ci.type.getUsedConstantsAsSet
      let mut hits : Array String := #[]
      for u in ts do
        let us := u.toString false
        if cone.contains us && !boring us then hits := hits.push us
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
        | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
      out := out.push s!"{item}\t{s}\t{kind}\t{cone.contains s}\t{modOf env n}\t{" ".intercalate hits.toList}"
  let cen := census env cone mods
  let mut ml : Array String := #[]
  for (m, (t, c, a)) in cen.toList do
    ml := ml.push s!"{m}\t{t}\t{c}\t{" ".intercalate a.toList}"
  IO.FS.writeFile (npiDir / "NPI_F2_names.tsv") ("\n".intercalate out.toList ++ "\n")
  IO.FS.writeFile (npiDir / "NPI_F2_modules.tsv") ("\n".intercalate ml.toList ++ "\n")
  logInfo s!"names={out.size} modules={ml.size}"

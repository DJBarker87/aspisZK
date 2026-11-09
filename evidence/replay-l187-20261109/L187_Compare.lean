import Lean
open Lean
/-! L187 structural object comparison. The olean embeds the source path given on the compiler
command line, so byte equality of replayed and overlay objects is not meaningful when the
original job used a different path. This tool compares module data: imports, constant names
(in order) and every ConstantInfo (types, values, theorem proofs, recursor rules). -/
namespace L187Compare
def eqDecl (a b : ConstantInfo) : Bool × Bool :=  -- (equal including proofs, equal ignoring theorem proofs)
  match a, b with
  | .thmInfo x, .thmInfo y => (x == y, x.toConstantVal == y.toConstantVal && x.all == y.all)
  | _, _ => let e := a == b; (e, e)
def compare (ov rp : System.FilePath) : IO Json := do
  let (da, ra) ← readModuleData ov
  let (db, rb) ← readModuleData rp
  let ia := da.imports.map (·.module.toString); let ib := db.imports.map (·.module.toString)
  let na := da.constNames; let nb := db.constNames
  let mut full := true; let mut modProofs := true; let mut firstDiff : Array String := #[]
  if na != nb then full := false; modProofs := false
  let mb : Std.HashMap Name ConstantInfo := db.constants.foldl (fun m c => m.insert c.name c) {}
  for c in da.constants do
    match mb[c.name]? with
    | none => full := false; modProofs := false; if firstDiff.size < 5 then firstDiff := firstDiff.push c.name.toString
    | some d =>
      let (e1, e2) := eqDecl c d
      if !e1 then full := false; if firstDiff.size < 5 then firstDiff := firstDiff.push c.name.toString
      if !e2 then modProofs := false
  ra.free; rb.free
  return Json.mkObj [("imports_equal", toJson (ia == ib)), ("const_names_equal", toJson (na == nb)),
    ("constants", toJson da.constants.size), ("identical_declarations", toJson full),
    ("identical_except_theorem_proofs", toJson modProofs), ("first_differing", toJson firstDiff)]
end L187Compare
/-- argv: input file with lines "module<TAB>overlay.olean<TAB>replay.olean", output jsonl. -/
unsafe def main (args : List String) : IO UInt32 := do
  let inp := args.getD 0 "L187_COMPARE_INPUT.tsv"; let outp := args.getD 1 "L187_COMPARE.jsonl"
  let h ← IO.FS.Handle.mk outp .write
  let mut bad := 0
  for line in ← IO.FS.lines inp do
    match line.splitOn "\t" with
    | [m, ov, rp] =>
      try
        let j ← L187Compare.compare ov rp
        h.putStrLn (Json.mkObj [("module", toJson m), ("result", j)]).compress
      catch e => bad := bad + 1; h.putStrLn (Json.mkObj [("module", toJson m), ("error", toJson e.toString)]).compress
    | _ => pure ()
  IO.println s!"L187_COMPARE_DONE errors={bad}"
  return 0

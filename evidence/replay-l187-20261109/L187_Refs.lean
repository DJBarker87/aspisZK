import Lean
open Lean
/-! L187 reference check: for a module object and a set of constant names, list the module's own
constants whose type or value mentions any of them (theorems flagged). argv: input tsv
"module<TAB>olean<TAB>name1,name2,...", output jsonl. One short process per call; regions are not freed. -/
unsafe def main (args : List String) : IO UInt32 := do
  let h ← IO.FS.Handle.mk (args.getD 1 "L187_REFS.jsonl") .write
  for line in ← IO.FS.lines (args.getD 0 "L187_REFS_INPUT.tsv") do
    match line.splitOn "\t" with
    | [m, ol, names] =>
      try
        let targets : NameSet := (names.splitOn ",").foldl (fun s n => s.insert n.toName) {}
        let (d, _r) ← readModuleData ol
        let mut users : Array Json := #[]
        for c in d.constants do
          let tyHits := c.type.getUsedConstants.filter targets.contains
          let valHits := ((c.value? true).map (·.getUsedConstants.filter targets.contains)).getD #[]
          if tyHits.size + valHits.size > 0 then
            users := users.push (Json.mkObj [("constant", toJson c.name.toString), ("is_theorem", toJson c.isTheorem),
              ("in_type", toJson (tyHits.map toString)), ("in_value", toJson (valHits.map toString))])
        let s := (Json.mkObj [("module", toJson m), ("users", toJson users)]).compress
        h.putStrLn s
      catch e => h.putStrLn (Json.mkObj [("module", toJson m), ("error", toJson e.toString)]).compress
    | _ => pure ()
  IO.println "L187_REFS_DONE"
  return 0

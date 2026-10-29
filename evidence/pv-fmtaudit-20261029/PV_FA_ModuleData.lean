import Lean
open Lean in
run_cmd do
  let path : System.FilePath := "/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029/object-pairs.tsv"
  let input ← IO.FS.readFile path
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    let xs := line.splitOn "\t"
    let [label, mod, left, right] := xs | throwError "bad object pair"
    let (a, _ar) ← readModuleData left
    let (b, _br) ← readModuleData right
    let kind (ci : ConstantInfo) : String := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | .thmInfo _ => "theorem" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .quotInfo _ => "quot"
    let mut am : NameMap ConstantInfo := {}
    let mut bm : NameMap ConstantInfo := {}
    for ci in a.constants do am := am.insert ci.name ci
    for ci in b.constants do bm := bm.insert ci.name ci
    let names := (a.constNames ++ b.constNames).toList.mergeSort (fun x y => x.toString < y.toString)
    let mut done : NameSet := {}
    let mut changes : Array Json := #[]
    for n in names do
      if done.contains n then continue
      done := done.insert n
      match am.find? n, bm.find? n with
      | some ac, some bc =>
        if kind ac != kind bc || ac.type != bc.type || ac.value? true != bc.value? true then
          changes := changes.push (Json.mkObj [("name", toJson (toString n)),("left_kind",toJson (kind ac)),("right_kind",toJson (kind bc)),("same_type",toJson (ac.type == bc.type)),("same_value",toJson (ac.value? true == bc.value? true))])
      | ac, bc =>
        changes := changes.push (Json.mkObj [("name",toJson (toString n)),("left_kind",toJson (ac.map kind)),("right_kind",toJson (bc.map kind))])
    let axs := b.constants.filterMap fun ci => if ci matches .axiomInfo _ then some (toString ci.name) else none
    let j := Json.mkObj [("label",toJson label),("module",toJson mod),("left",toJson left),("right",toJson right),("left_count",toJson a.constants.size),("right_count",toJson b.constants.size),("right_axiom_declarations",toJson axs),("changes",toJson changes)]
    logInfo m!"PV_FA_COMPARE {j.compress}"

import Aeneas
import Lean
open Lean in
run_cmd do
  let path : System.FilePath := "/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029/resume-object-pairs.tsv"
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


#print Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.Formatter
#print axioms Aeneas.Std.core.fmt.num.imp.DisplayUsize.fmt
open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !(toString mod).startsWith "Aeneas" then continue
    if ci matches .axiomInfo _ then
      logInfo m!"PV_FA_DECLARED_AXIOM {mod} {n}"

open Lean in
run_cmd do
  let input ← IO.FS.readFile "/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029/resume-footprint-inputs.tsv"
  let mut cache : Std.HashMap String ModuleData := {}
  let mut regions : Array CompactedRegion := #[]
  for line in input.splitOn "\n" do
    if line.isEmpty then continue
    let [id, root, path] := line.splitOn "\t" | throwError "bad input"
    let roots := path.splitOn ":" |>.map System.FilePath.mk
    let rootName := root.toName
    let rootMod := rootName.getPrefix
    let mut todo := [rootMod]
    let mut done : NameSet := {}
    let mut graph : NameMap (Array Name) := {}
    let mut axs : NameSet := {}
    let mut gaps : Array String := #[]
    let mut objects : Array Json := #[]
    while !todo.isEmpty do
      let m := todo.head!
      todo := todo.tail!
      if done.contains m then continue
      done := done.insert m
      let top := (m.toString.splitOn ".").head!
      if ["Init", "Lean", "Std", "Mathlib", "Batteries", "Aesop", "Qq"].contains top then continue
      let mut base : Option System.FilePath := none
      for r in roots do
        if (← (r / top).isDir) || (← (r / (top ++ ".olean")).pathExists) then
          base := some r
          break
      let some b := base | gaps := gaps.push s!"no namespace root: {m}"; continue
      let f := b / ((m.toString.replace "." "/") ++ ".olean")
      if !(← f.pathExists) then gaps := gaps.push s!"missing: {f}"; continue
      let data ← match cache[f.toString]? with
        | some d => pure d
        | none => do
          let (d, region) ← readModuleData f
          regions := regions.push region
          cache := cache.insert f.toString d
          pure d
      objects := objects.push (Json.mkObj [("module",toJson (toString m)),("path",toJson f.toString)])
      for imp in data.imports do todo := imp.module :: todo
      for ci in data.constants do
        let mut deps := ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[])
        if let .inductInfo v := ci then deps := deps ++ v.ctors.toArray
        graph := graph.insert ci.name deps
        if ci matches .axiomInfo _ then axs := axs.insert ci.name
    let mut cs := [rootName]
    let mut seen : NameSet := {}
    let mut fmt : NameSet := {}
    let mut usedAxs : NameSet := {}
    let mut unresolved : NameSet := {}
    while !cs.isEmpty do
      let n := cs.head!
      cs := cs.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if (toString n).startsWith "Aeneas.Std.core.fmt" then fmt := fmt.insert n
      if axs.contains n then usedAxs := usedAxs.insert n
      match graph.find? n with
      | some deps => cs := deps.toList ++ cs
      | none =>
        if (toString n).startsWith "Aeneas" || (toString n).startsWith "R1Z" || (toString n).startsWith "PV_" || (toString n).startsWith "Aspis" then unresolved := unresolved.insert n
    let j := Json.mkObj [("id",toJson id),("theorem",toJson root),("fmt_constants",toJson (fmt.toArray.map toString)),("used_nonstandard_axioms",toJson (usedAxs.toArray.map toString)),("unresolved_project_constants",toJson (unresolved.toArray.map toString)),("import_gaps",toJson gaps),("objects",toJson objects),("visited_constants",toJson seen.size)]
    logInfo m!"PV_FA_FOOTPRINT {j.compress}"

  logInfo m!"PV_FA_REGIONS {regions.size}"

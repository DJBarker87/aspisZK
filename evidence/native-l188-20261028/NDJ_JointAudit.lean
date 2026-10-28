import Lean
import JHx_Joint
set_option autoImplicit false
set_option pp.proofs false
set_option pp.all true
set_option pp.deepTerms true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
open Lean Elab Command
run_cmd logInfo "NDJ_POST_IMPORT"
#print axioms AspisR1.JHx_Joint.source
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`AspisR1.JHx_Joint.source] do
    let some info := env.checked.get.find? root | throwError "missing root {root}"
    logInfo m!"NDJ_KERNEL {(Json.mkObj [("name", toJson info.name.toString), ("levelParamsRepr", toJson (repr info.levelParams).pretty), ("typeRepr", toJson (repr info.type).pretty)]).compress}"
    let mut pending : Array Name := #[root]
    let mut seen : NameSet := ({} : NameSet).insert root
    while !pending.isEmpty do
      let n := pending.back!
      pending := pending.pop
      let some c := env.checked.get.find? n | throwError "missing reachable constant {n}"
      let mut refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
      if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
      for dep in refs do
        if !seen.contains dep then
          seen := seen.insert dep
          pending := pending.push dep
    let mut axioms : Array String := #[]
    for n in seen.toArray do
      if let some c := env.checked.get.find? n then
        if c.isAxiom then axioms := axioms.push n.toString
    logInfo m!"NDJ_ROOT {(Json.mkObj [("root", toJson root.toString), ("reachable", toJson seen.toArray.size), ("axioms", toJson axioms)]).compress}"
  let mut allAxioms : Array String := #[]
  for (n,c) in env.toKernelEnv.constants.toList do
    if c.isAxiom then allAxioms := allAxioms.push n.toString
  logInfo m!"NDJ_IMPORT_AXIOMS {toJson allAxioms |>.compress}"
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"NDJ_IMPORT {(Json.mkObj [("module", toJson m.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  logInfo "NDJ_AUDIT_COMPLETE"

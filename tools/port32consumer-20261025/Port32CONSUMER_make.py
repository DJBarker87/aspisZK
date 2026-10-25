"""Assemble one actual consumer; no compiler invocations."""
import pathlib,subprocess
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port32consumer-20261025'
def old(n):return (E/(n+'.lean.txt')).read_text()
lit=old('Port30JOIN_Literal');lit=lit[lit.index('open Lean\n'):].replace('Port30JOIN','Port32CONSUMER')
sel=old('Port30JOIN_Select');decode=sel[sel.index('def encodeName'):sel.index('structure Variant')]
# Retain exact355 dependency traversal: includes proj names, full opaque/rule bodies.
raw=subprocess.check_output(['git','show','HEAD:tools/port31data-20261025/Port31DATA_Raw355.lean'],text=True)
deps=raw[raw.index('private def expressionDeps'):raw.index('private def metadata')].replace('private def deps','def dependencies')
groups=sel[sel.index('def validateGroups'):sel.index('/-- Reachable checked-core axioms')].replace('Port30JOIN','Port32CONSUMER')
k=old('Port30JOIN_Kernel');k=k[k.index('namespace Port30JOIN_Kernel'):].replace('Port30JOIN_Kernel','Port32CONSUMER_Kernel').replace('Port30JOIN_Literal','Port32CONSUMER_Literal')
k=k.replace('  env : Kernel.Environment','  env : Environment').replace('  throw (IO.userError "Port30JOIN kernel insertion disabled")\n','').replace('  throw (IO.userError "Port30JOIN kernel calls disabled pending lead review/allocation")\n','').replace('private def replayDisabled','def replay').replace('env := env.toKernelEnv','env := env').replace('return .ofKernelEnv s.env','return s.env')
k=k.replace('replayConstants ci.getUsedConstantsAsSet','replayConstants ((Port32CONSUMER_Select.dependencies ci).foldl (fun s n => s.insert n) ({} : NameSet))')
k=k.replace('(← get).env.find?', '(← get).env.toKernelEnv.find?')
# Keep generated complete mutual inductives via ordinary kernel inductDecl; definitions
# are the original full definitions checked one by one, with group completeness guards.
consumer=old('Port30JOIN_Composed');consumer=consumer[consumer.index('set_option autoImplicit'):].replace('Port30JOIN','Port32CONSUMER')
src='''/- Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license. Authors: Kim Morrison.

Actual Port32CONSUMER: normal kernel reconstruction and concrete enclosing caller.
Only Lean is trust-imported. All project objects are raw DATA. See criteria/design.
Replay adapter copyright/license: Port32CONSUMER_ATTRIBUTION.md and LICENSE. -/
import Lean

namespace Port32CONSUMER
/-- New ordinary proof re-pin, not historical Bool helper identity. -/
theorem eq_true_of_not_eq_false {b : Bool} (h : b ≠ false) : b = true := by
  cases b with
  | false => exact False.elim (h rfl)
  | true => rfl
end Port32CONSUMER
/-- Explicit old-name compatibility shim. Actual original parse_header is rechecked below. -/
theorem Bool.eq_true_of_not_eq_false (b : Bool) (h : b ≠ false) : b = true :=
  @Port32CONSUMER.eq_true_of_not_eq_false b h
#print Port32CONSUMER.eq_true_of_not_eq_false
#print Bool.eq_true_of_not_eq_false
#print axioms Port32CONSUMER.eq_true_of_not_eq_false
#print axioms Bool.eq_true_of_not_eq_false

'''+lit+'\nnamespace Port32CONSUMER_Select\nopen Lean\n'+decode+'\n'+deps+'\n'+groups+'''
-- Regions remain in this process-global reference until EXIT. No region.free,
-- no semantic reference is serialized to or interpreted by Python.
initialize retained : IO.Ref (Array (ModuleData × CompactedRegion)) ← IO.mkRef #[]
initialize selectedRef : IO.Ref (Std.HashMap Name ConstantInfo) ← IO.mkRef {}
initialize coreNames : IO.Ref NameSet ← IO.mkRef {}

def jsonFile (p : String) : IO Json := do
  let s ← IO.FS.readFile p
  match Json.parse s with
  | .ok j => pure j
  | .error e => throw (IO.userError e)
def unwrap (x : Except String α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError e)
def standard (n : Name) : Bool := n == `propext || n == `Classical.choice || n == `Quot.sound

def load (env : Environment) : IO (Std.HashMap Name ConstantInfo) := do
  let j ← jsonFile "/private/tmp/Port32CONSUMER-20261025/Port32CONSUMER_selection.json"
  let os ← unwrap ((← unwrap (j.getObjVal? "origins")).getArr?)
  let mut origins : Array String := #[]
  for o in os do origins := origins.push (← unwrap o.getStr?)
  let mut choices : Std.HashMap Name String := {}
  for x in ← unwrap ((← unwrap (j.getObjVal? "choices")).getArr?) do
    let a ← unwrap x.getArr?
    unless a.size == 2 do throw (IO.userError "selection row arity")
    let n ← unwrap (decodeName 512 a[0]!)
    let i ← unwrap a[1]!.getNat?
    let some o := origins[i]? | throw (IO.userError "selection origin index")
    if choices.contains n then throw (IO.userError "duplicate actual Name choice")
    choices := choices.insert n o
  let files ← jsonFile "/private/tmp/Port32CONSUMER-20261025/Port32CONSUMER_groups.json"
  let mut selected : Std.HashMap Name ConstantInfo := {}
  for row in ← unwrap files.getArr? do
    let a ← unwrap row.getArr?
    unless a.size == 2 do throw (IO.userError "raw row arity")
    let o ← unwrap a[0]!.getStr?
    let path ← unwrap a[1]!.getStr?
    let part ← readModuleData ⟨path⟩
    retained.modify (·.push part)
    let d := part.1
    unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
        d.constNames == d.constants.map (·.name) do
      throw (IO.userError "not complete raw data")
    for c in d.constants do
      if choices[c.name]? != some o then continue
      if selected.contains c.name then throw (IO.userError "duplicate chosen declaration")
      if c.isUnsafe || c.isPartial || (c.isAxiom && !standard c.name) then
        throw (IO.userError s!"inadmissible selection {c.name}")
      match c with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless c.hasValue (allowOpaque := true) do throw (IO.userError "missing full body")
      | _ => pure ()
      selected := selected.insert c.name c
  unless selected.size == choices.size do throw (IO.userError "missing selection")
  -- ExactName closure; no arbitrary environment fallback and no new axiom.
  for (_,c) in selected.toList do
    for n in dependencies c do
      unless selected.contains n || n == `Bool.eq_true_of_not_eq_false do
        throw (IO.userError s!"unselected dependency {n} in {c.name}")
  validateGroups selected env
  let mut reused : NameSet := {}
  let mut coreManifest : Array Json := #[]
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  for (n,c) in selected.toList do
    if let some old := env.toKernelEnv.find? n then
      unless Port32CONSUMER_Literal.strictDeclaration old c do
        throw (IO.userError s!"selected CI differs from checked core: {n}; origin={choices[n]!}")
      let some mi := env.getModuleIdxFor? n
        | throw (IO.userError s!"existing selected name has no core origin {n}")
      let some mod := env.header.modules[mi.toNat]?
        | throw (IO.userError "bad core module index")
      unless (`Init).isPrefixOf mod.module || (`Lean).isPrefixOf mod.module ||
          (`Std).isPrefixOf mod.module do
        throw (IO.userError s!"non-core trust origin {mod.module}")
      coreManifest := coreManifest.push (Json.mkObj [("name",encodeName n),("selected_origin",toJson choices[n]!),
        ("core_module",encodeName mod.module),("axiom",toJson c.isAxiom),("unsafe",toJson c.isUnsafe),("partial",toJson c.isPartial)])
      reused := reused.insert n
    else
      if c.isAxiom then throw (IO.userError "new axiom rejected")
      fresh := fresh.insert n c
  IO.FS.writeFile "/private/tmp/Port32CONSUMER-20261025/Port32CONSUMER_core-manifest.json" (Json.arr coreManifest).compress
  selectedRef.set selected
  coreNames.set reused
  IO.println s!"PORT32_SELECTION names={selected.size} fresh={fresh.size} strict-core={reused.size}"
  return fresh
end Port32CONSUMER_Select

'''+k+'''
open Lean in
run_elab do
  let env ← getEnv
  logInfo m!"PORT32_IMPORTS {env.header.modules.map (·.module)}"
  let fresh ← Port32CONSUMER_Select.load env
  let checked ← Port32CONSUMER_Kernel.replay fresh env
  -- No unchecked insertion: every fresh declaration above went through addDeclCore.
  -- Existing core constants were checked against their entire selected CI.
  setEnv checked
  let selected ← Port32CONSUMER_Select.selectedRef.get
  for (n,c) in selected.toList do
    let some d := checked.toKernelEnv.find? n | throwError "missing checked {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do
      throwError "strict checked-CI/source readback failed {n}"
  logInfo m!"PORT32_FULL_STRICT_READBACK {selected.size}"

macro:max x:term:max noWs "#usize" : term =>
  `(Aeneas.Std.Usize.ofNat $x (by decide))

'''+consumer+'''
set_option pp.all true in
#print Port32CONSUMER.accepted_original_sdk_s2_s1
#print axioms AspisR1.OraclePortCompactDraft.parse_header
#print axioms AspisR1.S2W_D189Consolidation.accepted_run
#print axioms AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace
#print axioms AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts

open Lean in
run_elab do
  for n in #[`Port32CONSUMER.eq_true_of_not_eq_false, `Bool.eq_true_of_not_eq_false,
      `AspisR1.OraclePortCompactDraft.parse_header,
      `AspisR1.S2W_D189Consolidation.accepted_run,
      `AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace,
      `AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts,
      `Port32CONSUMER.accepted_original_sdk_s2_s1] do
    let some c := (← getEnv).toKernelEnv.find? n | throwError "missing audit target {n}"
    unless c.isTheorem do throwError "audit target not theorem {n}"
    let axs ← collectAxioms n
    unless axs.all Port32CONSUMER_Select.standard do throwError "rejected axioms {n}: {axs}"
    logInfo m!"PORT32_AXIOMS {n}: {axs}"
  let selected ← Port32CONSUMER_Select.selectedRef.get
  for (n,c) in selected.toList do
    let some d := (← getEnv).toKernelEnv.find? n | throwError "missing final CI {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do throwError "final CI drift {n}"
  let regions ← Port32CONSUMER_Select.retained.get
  logInfo m!"PORT32_COMPLETE selected={selected.size} retained_regions={regions.size}"
'''
(T/'Port32CONSUMER_Consumer.lean').write_text(src)
print('assembled',len(src),'bytes; import Lean only')

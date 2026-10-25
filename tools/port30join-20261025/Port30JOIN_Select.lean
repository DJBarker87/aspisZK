/- UNCOMPILED data-only preparation. No command elaborator, #eval or main.
Raw regions are retained for the entire process containing checked terms.
No returned Name/Expr/ConstantInfo may outlive this session; no region.free here.
No imported project environments are retained. Minimal raw fragments only. -/
import Lean
import Port30JOIN_Literal
open Lean
namespace Port30JOIN_Select

def encodeName : Name → Json
  | .anonymous => toJson (["anon"] : List String)
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson (String.ofList s.toList)]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

def decodeName : Nat → Json → Except String Name
  | 0, _ => .error "Name depth exceeds bound"
  | fuel+1, j => do
    let a ← j.getArr?
    match a.toList with
    | [.str "anon"] => pure .anonymous
    | [.str "str",p,.str s] => pure (.str (← decodeName fuel p) s)
    | [.str "num",p,.str s] =>
      let some n := s.toNat? | throw "invalid Name.num"
      unless toString n == s do throw "noncanonical Name.num"
      pure (.num (← decodeName fuel p) n)
    | _ => throw "invalid exact Name encoding"

structure Variant where
  origin : String
  declaration : ConstantInfo

/-- This is a declared selection, never a literal equality certificate. -/
inductive SelectionMode where
  | literal
  | recheckCurrent

structure Choice where
  name : Name
  origin : String
  mode : SelectionMode

structure RawSession where
  parts : Array (ModuleData × CompactedRegion)
  variants : Std.HashMap Name (Array Variant)

/-- Caller preflight must pin bytes, regular-file authority and <=512MiB total.
Raw fragments are individual, additive files, never trusted imports. -/
def readRawSession (files : Array (String × System.FilePath)) : IO RawSession := do
  let mut parts := #[]
  let mut variants : Std.HashMap Name (Array Variant) := {}
  for (origin,path) in files do
    let part ← readModuleData path
    parts := parts.push part
    let d := part.1
    unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
        d.constNames == d.constants.map (·.name) do
      throw (IO.userError "non-raw or incomplete fragment")
    for c in d.constants do
      let old := variants[c.name]?.getD #[]
      if old.any (fun v => v.origin == origin) then
        throw (IO.userError s!"duplicate origin identifier at {c.name}")
      variants := variants.insert c.name (old.push ⟨origin,c⟩)
  pure ⟨parts,variants⟩

/-- Full opaque values and mutual/constructor/rule edges, actual Name only.
No String.toName. Normal replay handles inductive groups atomically. -/
def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ds := c.type.getUsedConstants
  if let some v := c.value? (allowOpaque := true) then ds := ds ++ v.getUsedConstants
  match c with
  | .inductInfo v =>
    ds := ds ++ v.all.toArray ++ v.ctors.toArray
    for n in v.all do ds := ds.push (n.str "rec")
  | .defnInfo v => ds := ds ++ v.all.toArray
  | .thmInfo v => ds := ds ++ v.all.toArray
  | .opaqueInfo v => ds := ds ++ v.all.toArray
  | .ctorInfo v => ds := ds.push v.induct
  | .recInfo v =>
    ds := ds ++ v.all.toArray
    for n in v.all do ds := ds.push (n.str "rec")
    for r in v.rules do ds := (ds.push r.ctor) ++ r.rhs.getUsedConstants
  | _ => pure ()
  return ds

/-- Preserve all variants in session. Explicit decisions required even for
singleton names. Nonliteral chosen terms must be checked as a NEW re-pin. -/
def select (session : RawSession) (choices : Array Choice) (seeds : Array Name)
    (core : Environment) : IO (Std.HashMap Name ConstantInfo) := do
  let mut todo := seeds.toList
  let mut selected : Std.HashMap Name ConstantInfo := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if selected.contains n then continue
    let vs := session.variants[n]?.getD #[]
    if vs.isEmpty then
      -- No project fallback; only already checked core entries may be leaves.
      unless (core.toKernelEnv.find? n).isSome do
        throw (IO.userError s!"missing exact dependency {n}")
      continue
    let cs := choices.filter (fun c => c.name == n)
    unless cs.size == 1 do throw (IO.userError s!"missing/ambiguous choice {n}")
    let choice := cs[0]!
    let some chosen := vs.find? (fun v => v.origin == choice.origin)
      | throw (IO.userError s!"missing chosen origin {n}")
    let c := chosen.declaration
    if c.isAxiom then
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throw (IO.userError s!"project axiom {n}")
      let some old := core.toKernelEnv.find? n
        | throw (IO.userError s!"missing pinned standard axiom {n}")
      unless old.isAxiom && Port30JOIN_Literal.strictDeclaration old c do
        throw (IO.userError s!"changed standard axiom {n}")
      continue
    if c.isUnsafe || c.isPartial then
      throw (IO.userError s!"inadmissible logical declaration {n}")
    match choice.mode with
    | .literal =>
      for v in vs do
        unless Port30JOIN_Literal.strictDeclaration c v.declaration do
          throw (IO.userError s!"nonliteral origins require explicit re-pin {n}")
    | .recheckCurrent => pure () -- does not certify equivalence; kernel still mandatory
    if let some old := core.toKernelEnv.find? n then
      unless Port30JOIN_Literal.strictDeclaration old c do
        throw (IO.userError s!"selected raw conflicts with checked core {n}")
    selected := selected.insert n c
    todo := (dependencies c).toList ++ todo
  pure selected
/-- Must run before replay, in addition to transitive expression closure.
Reject incomplete or mismatched mutual/constructor/recursor groups. -/
def validateGroups (selected : Std.HashMap Name ConstantInfo) (core : Environment) : IO Unit := do
  let find := fun n => (selected[n]?).orElse (fun _ => core.toKernelEnv.find? n)
  for (n,c) in selected.toList do
    unless c.name == n do throw (IO.userError "map key/name mismatch")
    match c with
    | .inductInfo v =>
      unless v.all.contains n do throw (IO.userError "inductive missing self")
      for m in v.all do
        let some (.inductInfo w) := find m
          | throw (IO.userError s!"missing mutual inductive {m}")
        unless w.all == v.all && w.levelParams == v.levelParams && w.numParams == v.numParams do
          throw (IO.userError "inconsistent inductive group header")
        for ctor in w.ctors do
          let some (.ctorInfo x) := find ctor
            | throw (IO.userError s!"missing constructor {ctor}")
          unless x.induct == m && x.levelParams == w.levelParams && x.numParams == w.numParams do
            throw (IO.userError "constructor group mismatch")
        let recName := m.str "rec"
        let some (.recInfo r) := find recName
          | throw (IO.userError s!"missing recursor {recName}")
        unless r.all == v.all do throw (IO.userError "recursor group mismatch")
    | .ctorInfo v =>
      let some (.inductInfo i) := find v.induct
        | throw (IO.userError "orphan constructor")
      unless i.ctors.contains n do throw (IO.userError "unlisted constructor")
    | .recInfo v =>
      for m in v.all do
        let some (.inductInfo _) := find m
          | throw (IO.userError "orphan recursor")
    | .defnInfo v =>
      for m in v.all do
        unless (find m).isSome do throw (IO.userError "incomplete definition group")
    | .thmInfo v =>
      for m in v.all do
        unless (find m).isSome do throw (IO.userError "incomplete theorem group")
    | .opaqueInfo v =>
      for m in v.all do
        unless (find m).isSome do throw (IO.userError "incomplete opaque group")
    | _ => pure ()
/-- Reachable checked-core axioms are audited too: a missing raw sorryAx cannot
silently become an admitted core leaf. This audit is data inspection only. -/
def auditCoreLeaves (selected : Std.HashMap Name ConstantInfo) (core : Environment) : IO Unit := do
  let mut todo := selected.toList.flatMap (fun (_,c) => (dependencies c).toList)
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if selected.contains n || seen.contains n then continue
    seen := seen.insert n
    let some c := core.toKernelEnv.find? n
      | throw (IO.userError s!"missing core leaf {n}")
    if c.isAxiom then
      unless n == `propext || n == `Classical.choice || n == `Quot.sound do
        throw (IO.userError s!"nonstandard reachable axiom {n}")
    else
      if c.isUnsafe || c.isPartial then throw (IO.userError s!"unsafe core leaf {n}")
      todo := (dependencies c).toList ++ todo
end Port30JOIN_Select

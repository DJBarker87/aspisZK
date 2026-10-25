import Lean
open Lean
namespace Port35ANCHOR_Literal
-- Exact accepted Port18 helpers; readComplete is retained for copy assessment,
-- All raw regions remain mapped until OS exit; none are freed.
def sameDeclaration (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false
-- Strict-v3 retains the entire accepted metadata comparison and adds checks
-- for every expression field, including metadata representation ignored by BEq.
private def rawSliceEq (a b : Substring.Raw) : Bool :=
  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos
private def sourceInfoEq : SourceInfo → SourceInfo → Bool
  | .none, .none => true
  | .original a p b q, .original c r d s =>
      rawSliceEq a c && p == r && rawSliceEq b d && q == s
  | .synthetic p q c, .synthetic r s d => p == r && q == s && c == d
  | _, _ => false
private partial def syntaxEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node i k xs, .node j l ys => sourceInfoEq i j && k == l && xs.isEqv ys syntaxEq
  | .atom i v, .atom j w => sourceInfoEq i j && v == w
  | .ident i r n ps, .ident j s m qs =>
      sourceInfoEq i j && rawSliceEq r s && n == m && ps == qs
  | _, _ => false
private def dataValueEq (a b : DataValue) : Bool :=
  match a,b with
  | .ofSyntax x, .ofSyntax y => syntaxEq x y
  | _,_ => a == b
private def mdataEq (a b : MData) : Bool :=
  a.entries.isEqv b.entries (fun (k,v) (l,w) => k == l && dataValueEq v w)
-- Iterative walk avoids changing recursion-depth limits. No expression escapes.
def strictExpr (a b : Expr) : Bool := Id.run do
  if !Expr.equal a b then return false
  let mut todo := #[(a,b)]
  while !todo.isEmpty do
    let (x,y) := todo.back!
    todo := todo.pop
    match x,y with
    | .app f a, .app g b => todo := (todo.push (f,g)).push (a,b)
    | .lam n t v bi, .lam m u w bj
    | .forallE n t v bi, .forallE m u w bj =>
      if n != m || bi != bj then return false
      todo := (todo.push (t,u)).push (v,w)
    | .letE n t v e d, .letE m u w f c =>
      if n != m || d != c then return false
      todo := ((todo.push (t,u)).push (v,w)).push (e,f)
    | .mdata m e, .mdata n f =>
      if !mdataEq m n then return false
      todo := todo.push (e,f)
    | .proj n i e, .proj m j f =>
      if n != m || i != j then return false
      todo := todo.push (e,f)
    | .bvar i, .bvar j => if i != j then return false
    | .fvar i, .fvar j => if i != j then return false
    | .mvar i, .mvar j => if i != j then return false
    | .sort u, .sort v => if u != v then return false
    | .const n us, .const m vs => if n != m || us != vs then return false
    | .lit v, .lit w => if v != w then return false
    | _,_ => return false
  return true
private def strictValue (a b : ConstantInfo) : Bool :=
  match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
  | none, none => true
  | some x, some y => strictExpr x y
  | _,_ => false
private def strictRules (a b : ConstantInfo) : Bool :=
  match a,b with
  | .recInfo x, .recInfo y =>
    x.rules.isEqv y.rules (fun r s => r.ctor == s.ctor && r.nfields == s.nfields && strictExpr r.rhs s.rhs)
  | .recInfo _,_ | _,.recInfo _ => false
  | _,_ => true
def strictDeclaration (a b : ConstantInfo) : Bool :=
  sameDeclaration a b && strictExpr a.type b.type && strictValue a b && strictRules a b
private def strictConstantVal (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && strictExpr a.type b.type


end Port35ANCHOR_Literal

namespace Port35ANCHOR_Select
open Lean
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


private def expressionDeps (e : Expr) : Array Name := Id.run do
  let mut todo := #[e]
  let mut seen : Std.HashSet Expr := {}
  let mut names : Std.HashSet Name := {}
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ => names := names.insert n
    | .proj n _ v =>
      names := names.insert n
      todo := todo.push v
    | .app f a => todo := (todo.push f).push a
    | .lam _ t v _ | .forallE _ t v _ => todo := (todo.push t).push v
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ v => todo := todo.push v
    | _ => pure ()
  return names.toArray
def dependencies (c : ConstantInfo) : Array Name := Id.run do
  let mut ds := expressionDeps c.type
  if let some v := c.value? (allowOpaque := true) then ds := ds ++ expressionDeps v
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
    for r in v.rules do ds := (ds.push r.ctor) ++ expressionDeps r.rhs
  | _ => pure ()
  let mut out : Std.HashSet Name := {}
  for n in ds do out := out.insert n
  return out.toArray

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

-- All loaded ModuleData/regions travel in the same command's lexical owner.
-- No explicit free and no finalizer: mapped buffers remain until process EXIT.
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

def load (env : Environment) : IO (Std.HashMap Name ConstantInfo × Std.HashMap Name ConstantInfo × Array (ModuleData × CompactedRegion)) := do
  let j ← jsonFile "/Users/dominic/ZK/.worktrees/cx-port35-anchor/evidence/port35anchor-20261025/Port35ANCHOR_selection.json"
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
  let files ← jsonFile "/Users/dominic/ZK/.worktrees/cx-port35-anchor/evidence/port35anchor-20261025/Port35ANCHOR_groups.json"
  let mut selected : Std.HashMap Name ConstantInfo := {}
  let mut regions : Array (ModuleData × CompactedRegion) := #[]
  for row in ← unwrap files.getArr? do
    let a ← unwrap row.getArr?
    unless a.size == 2 do throw (IO.userError "raw row arity")
    let o ← unwrap a[0]!.getStr?
    let path ← unwrap a[1]!.getStr?
    let part ← readModuleData ⟨path⟩
    regions := regions.push part
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
      unless selected.contains n do
        throw (IO.userError s!"unselected dependency {n} in {c.name}")
  validateGroups selected env
  let mut reused : NameSet := {}
  let mut coreManifest : Array Json := #[]
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  for (n,c) in selected.toList do
    if let some old := env.toKernelEnv.find? n then
      unless Port35ANCHOR_Literal.strictDeclaration old c do
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
  IO.FS.writeFile "/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR_core-manifest.json" (Json.arr coreManifest).compress
  IO.println s!"PORT32_SELECTION names={selected.size} fresh={fresh.size} strict-core={reused.size}"
  return (fresh,selected,regions)
end Port35ANCHOR_Select

namespace Port35ANCHOR_Kernel
open Lean

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore (Core.getMaxHeartbeats {}).toUSize d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ((Port35ANCHOR_Select.dependencies ci).foldl (fun s n => s.insert n) ({} : NameSet))
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          addDecl (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          -- Make sure we are really finished with the constructors.
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        -- We postpone checking constructors,
        -- and at the end make sure they are identical
        -- to the constructors generated when we replay the inductives.
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        -- Similarly we postpone checking recursors.
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          -- `Quot.lift` and `Quot.ind` have types that reference `Eq`,
          -- so we need to ensure `Eq` is replayed before adding the quotient declaration.
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
        IO.println s!"PORT35_CHECKED {name}"
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if !Port35ANCHOR_Literal.strictDeclaration (.ctorInfo info) (.ctorInfo info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !Port35ANCHOR_Literal.strictDeclaration (.recInfo info) (.recInfo info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay

/--
"Replay" some constants into an `Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.
-/
def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) : IO Kernel.Environment := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if ci.isUnsafe || ci.isPartial then
      throw (IO.userError s!"unsafe/partial project declaration {n}")
    if ci.isAxiom then throw (IO.userError s!"project axiom {n}")
    remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env := env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  unless s.remaining.isEmpty && s.pending.isEmpty do
    throw (IO.userError "unfinished replay group")
  return s.env
end Port35ANCHOR_Kernel

namespace Port35ANCHOR
open Lean
def oldCalls := `AspisR1PublicPreparation.Query31SourceSchedule.queries_success_with_digest_pairs_full
def oldBridge := `AspisR1PublicPreparation.Query31SourceSchedule.queries_success_pairs_functional_full
def newCalls := `Port35ANCHOR.queries_success_with_digest_pairs_full
def pairName := `AspisR1PublicPreparation.Query31SourceSchedule.DigestPair
def pairState := pairName.str "state"
def transcriptHash := `AspisR1PublicPreparation.transcript.Transcript.hash
def transcriptState := `AspisR1PublicPreparation.transcript.Transcript.state
def chainName := `AspisR1PublicPreparation.Query31SourceSchedule.stateChain
def materialName := `AspisR1PublicPreparation.Query31SourceSchedule.materializedOutputs

def app? (n : Name) (arity : Nat) (e : Expr) : Option (Array Expr) :=
  if e.getAppFn.isConstOf n && e.getAppNumArgs == arity then some e.getAppArgs else none

def tail? (e : Expr) : Option (Array Expr) := do
  let a ← app? `And 2 e
  let c ← app? chainName 4 a[0]!
  let m ← app? materialName 6 a[1]!
  unless (List.range 4).all (fun i => Port35ANCHOR_Literal.strictExpr c[i]! m[i]!) do none
  let hash ← app? transcriptHash 2 c[2]!
  unless Port35ANCHOR_Literal.strictExpr c[0]! hash[0]! do none
  return c.push hash[1]!

def andE (a b : Expr) := mkApp2 (mkConst `And) a b
def andI (a b ha hb : Expr) := mkApp4 (mkConst `And.intro) a b ha hb
def eqE (t a b : Expr) := mkApp3 (mkConst `Eq [Level.one]) t a b
def refl (t a : Expr) := mkApp2 (mkConst `Eq.refl [Level.one]) t a
def existsE (t p : Expr) := mkApp2 (mkConst `Exists [Level.one]) t p
def existsI (t p x h : Expr) := mkApp4 (mkConst `Exists.intro [Level.one]) t p x h

def anchor (stateTy : Expr) (c : Array Expr) : Expr := Id.run do
  let ty := mkApp3 (mkConst pairName) c[0]! c[1]! c[2]!
  let lty := mkApp (mkConst `List [Level.zero]) ty
  let lifted := c.map (fun e => e.liftLooseBVars 0 2)
  let first := mkBVar 1
  let rest := mkBVar 0
  let listEq := eqE (lty.liftLooseBVars 0 2) lifted[3]!
    (mkApp3 (mkConst `List.cons [Level.zero]) (ty.liftLooseBVars 0 2) first rest)
  let stateEq := eqE stateTy (mkApp4 (mkConst pairState) lifted[0]! lifted[1]! lifted[2]! first)
    (mkApp2 (mkConst transcriptState) lifted[0]! lifted[4]!)
  let inner := existsE (lty.liftLooseBVars 0 1)
    (.lam `rest (lty.liftLooseBVars 0 1) (andE listEq stateEq) .default)
  return existsE ty (.lam `first ty inner .default)

structure StrictKey where
  val : Expr
instance : BEq StrictKey := ⟨fun a b => Port35ANCHOR_Literal.strictExpr a.val b.val⟩
instance : Hashable StrictKey := ⟨fun a => a.val.hash⟩

def children (e : Expr) : Array Expr :=
  match e with
  | .app f a => #[f,a]
  | .lam _ t b _ | .forallE _ t b _ => #[t,b]
  | .letE _ t v b _ => #[t,v,b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

def countTails (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet StrictKey := {}
  let mut todo := #[e]
  let mut n := 0
  while !todo.isEmpty do
    let x := todo.back!; todo := todo.pop
    if seen.contains ⟨x⟩ then continue
    seen := seen.insert ⟨x⟩
    if (tail? x).isSome then n := n + 1
    todo := todo ++ children x
  return n

def strengthen (stateTy e : Expr) : Expr :=
  e.replace fun x => (tail? x).map (fun c => andE (anchor stateTy c) x)

-- Only typed explicit let constructors supply the witness. No length/chain inference.
def localLet (ctx : Array (Name × Option Expr)) (e : Expr) : Except String (Name × Expr) := do
  let .bvar k := e | throw "expected local let reference"
  let some (n,some v) := ctx[ctx.size - 1 - k]? | throw "missing let binder"
  return (n,v.liftLooseBVars 0 (k+1))

def witness (ctx : Array (Name × Option Expr)) (stateTy : Expr) (c : Array Expr) : Except String Expr := do
  let (pn,list) ← localLet ctx c[3]!
  unless pn == `pairs do throw "wrong pairs binder"
  let some cons := app? `List.cons 3 list | throw "pairs is not literal cons"
  let first := cons[1]!; let rest := cons[2]!
  let (n0,p0) ← localLet ctx first
  unless n0 == `pair0 do throw "head is not pair0"
  let some ctor := app? (pairName.str "mk") 10 p0 | throw "pair0 constructor/arity mismatch"
  unless Port35ANCHOR_Literal.strictExpr ctor[3]! (mkApp2 (mkConst transcriptState) c[0]! c[4]!) do
    throw "pair0 state is not absorbed.state"
  let mut cursor := list
  for i in [:8] do
    let some cs := app? `List.cons 3 cursor | throw "short explicit list"
    let (nm,_) ← localLet ctx cs[1]!
    unless nm == Name.str .anonymous ("pair" ++ toString i) do throw "pair order mismatch"
    cursor := cs[2]!
  unless (app? `List.nil 1 cursor).isSome do throw "non-eight list"
  let a := anchor stateTy c
  let aa := a.getAppArgs
  let inner := aa[1]!.bindingBody!.instantiate1 first
  let ia := inner.getAppArgs
  let body := ia[1]!.bindingBody!.instantiate1 rest
  let ba := body.getAppArgs
  let hp := andI ba[0]! ba[1]! (refl ia[0]! c[3]!)
    (refl stateTy (mkApp2 (mkConst transcriptState) c[0]! c[4]!))
  return existsI aa[0]! aa[1]! first (existsI ia[0]! ia[1]! rest hp)

-- Bounded structural diagnostic walks actual Expr, carrying actual binder scopes.
def repairValue (stateTy e : Expr) : IO (Expr × Json) := do
  let mut todo := #[(e, (#[] : Array (Name × Option Expr)))]
  let mut seen : Std.HashSet StrictKey := {}
  let mut patches : Array (Expr × Expr) := #[]
  let mut reports : Array Json := #[]
  while !todo.isEmpty do
    let (x,ctx) := todo.back!; todo := todo.pop
    if seen.contains ⟨x⟩ then continue
    seen := seen.insert ⟨x⟩
    if let some a := app? `And.intro 4 x then
      if let some c := tail? (andE a[0]! a[1]!) then
        let hp ← Port35ANCHOR_Select.unwrap (witness ctx stateTy c)
        let oldTail := andE a[0]! a[1]!
        patches := patches.push (x,andI (anchor stateTy c) oldTail hp x)
        reports := reports.push (Json.mkObj [("scope_depth",toJson ctx.size),
          ("pairs_expr",toJson (toString c[3]!)),("absorbed_expr",toJson (toString c[4]!)),
          ("binder_names",toJson (ctx.map (fun (n,_) => toString n))),
          ("anchor_type",toJson (toString (anchor stateTy c))),
          ("witness",toJson (toString hp))])
    match x with
    | .lam n t b _ | .forallE n t b _ =>
      todo := (todo.push (t,ctx)).push (b,ctx.push (n,none))
    | .letE n t v b _ =>
      todo := ((todo.push (t,ctx)).push (v,ctx)).push (b,ctx.push (n,some v))
    | _ => for y in children x do todo := todo.push (y,ctx)
  IO.FS.writeFile "/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR-structural.json"
    (Json.mkObj [("patches",toJson patches.size),("nodes",toJson seen.size),("sites",Json.arr reports)]).pretty
  unless patches.size == 1 do throw (IO.userError s!"unexpected terminal proof patch count {patches.size}")
  let (src,dst) := patches[0]!
  return (e.replace (fun x => if Port35ANCHOR_Literal.strictExpr x src then some dst else none),Json.arr reports)

-- Kernel-only transitive axiom walk; every visited name must exist.
def audit (env : Kernel.Environment) (root : Name) : IO Json := do
  let some c := env.find? root | throw (IO.userError s!"missing audit target {root}")
  unless c.isTheorem do throw (IO.userError "audit target not theorem")
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut leaves : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some d := env.find? n | throw (IO.userError s!"missing audit dependency {n}")
    if d.isUnsafe || d.isPartial then throw (IO.userError s!"unsafe audit dependency {n}")
    if d.isAxiom then
      unless Port35ANCHOR_Select.standard n do throw (IO.userError s!"nonstandard axiom {n}")
      leaves := leaves.insert n
    else todo := todo ++ Port35ANCHOR_Select.dependencies d
  IO.println s!"#print axioms {root}: {leaves.toList}"
  return Json.mkObj [("target",Port35ANCHOR_Select.encodeName root),
    ("full_axioms",toJson (leaves.toList.map toString)),("visited",toJson seen.size)]

def run (core : Environment) : IO Unit := do
  IO.FS.createDirAll "/private/tmp/Port35ANCHOR-20261025"
  let (fresh,selected,regions) ← Port35ANCHOR_Select.load core
  let some (.thmInfo calls) := selected[oldCalls]? | throw (IO.userError "missing actual Calls")
  let some (.thmInfo bridge) := selected[oldBridge]? | throw (IO.userError "missing actual Bridge")
  let some stateCI := selected[transcriptState]? | throw (IO.userError "missing state projection")
  let mut stateTy := stateCI.type
  while stateTy.isForall do stateTy := stateTy.bindingBody!
  unless !stateTy.hasLooseBVars do throw (IO.userError "state carrier unexpectedly dependent")
  let typeSites := countTails calls.type
  let valueSites := countTails calls.value
  unless typeSites == 1 && valueSites > 5 do throw (IO.userError "stale type/motive shape")
  let strongType := strengthen stateTy calls.type
  let restoredType := strongType.replace fun x => do
    let a ← app? `And 2 x
    let c ← tail? a[1]!
    unless Port35ANCHOR_Literal.strictExpr a[0]! (anchor stateTy c) do none
    return a[1]!
  unless Port35ANCHOR_Literal.strictExpr calls.type restoredType do
    throw (IO.userError "type delta changed more than anchor insertion")
  let motives := strengthen stateTy calls.value
  let (strongValue,sites) ← repairValue stateTy motives
  let strong : TheoremVal := {calls with name := newCalls, type := strongType, value := strongValue, all := [newCalls]}
  let mut bridgeCount := 0
  let mut todo := #[bridge.value]
  while !todo.isEmpty do
    let e := todo.back!; todo := todo.pop
    if e.isConstOf oldCalls then bridgeCount := bridgeCount + 1
    todo := todo ++ children e
  unless bridgeCount == 1 do throw (IO.userError s!"Bridge Calls reference count {bridgeCount}")
  let revised : TheoremVal := {bridge with value := bridge.value.replace fun e =>
    match e with
    | .const n ls => if n == oldCalls then some (.const newCalls ls) else none
    | _ => none}
  unless Port35ANCHOR_Literal.strictExpr bridge.type revised.type && bridge.levelParams == revised.levelParams &&
    bridge.name == revised.name && bridge.all == revised.all do throw (IO.userError "Bridge header drift")
  -- An inverse syntactic replacement certifies the entire remaining Bridge value.
  let restored := revised.value.replace fun e =>
    match e with
    | .const n ls => if n == newCalls then some (.const oldCalls ls) else none
    | _ => none
  unless Port35ANCHOR_Literal.strictExpr restored bridge.value do throw (IO.userError "Bridge delta is not minimal")
  IO.FS.writeFile "/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR-types.json"
    (Json.mkObj [("before_calls_type",toJson (toString calls.type)),("after_calls_type",toJson (toString strongType)),
      ("before_bridge_type",toJson (toString bridge.type)),("after_bridge_type",toJson (toString revised.type)),
      ("calls_type_sites",toJson typeSites),("calls_motive_sites",toJson valueSites),
      ("bridge_reference_delta",toJson bridgeCount),("sites",sites),
      ("status",toJson "CONSTRUCTED; not yet checked")]).pretty
  IO.println s!"PORT35_CONSTRUCTED typeSites={typeSites} motiveSites={valueSites} bridgeDelta={bridgeCount}"
  let checked ← Port35ANCHOR_Kernel.replay (fresh.erase oldBridge) core.toKernelEnv
  for (n,c) in selected.toList do
    if n == oldBridge then continue
    let some d := checked.find? n | throw (IO.userError s!"missing checked declaration {n}")
    unless Port35ANCHOR_Literal.strictDeclaration c d do throw (IO.userError s!"strict checked readback {n}")
  let checked ← match checked.addDeclCore (Core.getMaxHeartbeats {}).toUSize (.thmDecl strong) (cancelTk? := none) with
    | .ok e => pure e
    | .error ex => throw (IO.userError (← ex.toMessageData {} |>.toString))
  IO.println "PORT35_STRONG_CHECKED"
  let checked ← match checked.addDeclCore (Core.getMaxHeartbeats {}).toUSize (.thmDecl revised) (cancelTk? := none) with
    | .ok e => pure e
    | .error ex => throw (IO.userError (← ex.toMessageData {} |>.toString))
  IO.println "PORT35_BRIDGE_CHECKED"
  let mut audits := #[]
  for n in #[oldCalls,newCalls,oldBridge] do audits := audits.push (← audit checked n)
  let delta := #[ConstantInfo.thmInfo strong,ConstantInfo.thmInfo revised]
  for c in delta do
    let some d := checked.find? c.name | throw (IO.userError "missing delta readback")
    unless Port35ANCHOR_Literal.strictDeclaration c d do throw (IO.userError "checked delta drift")
  saveModuleData ⟨"/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR-checked-delta.olean"⟩ `Port35ANCHOR.RawDelta {
    isModule := false, imports := #[], constNames := delta.map (·.name), constants := delta, extraConstNames := #[], entries := #[] }
  let readback ← readModuleData ⟨"/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR-checked-delta.olean"⟩
  unless readback.1.imports.isEmpty && readback.1.extraConstNames.isEmpty && readback.1.entries.isEmpty &&
      readback.1.constNames == delta.map (·.name) && readback.1.constants.size == delta.size do
    throw (IO.userError "delta header")
  for i in [:delta.size] do
    unless Port35ANCHOR_Literal.strictDeclaration delta[i]! readback.1.constants[i]! do
      throw (IO.userError "strict same-invocation complete-CI delta readback")
  IO.FS.writeFile "/private/tmp/Port35ANCHOR-20261025/Port35ANCHOR-result.json"
    (Json.mkObj [("status",toJson "PASS normally checked strengthened Calls and minimal Bridge proof re-pin"),
      ("selected",toJson selected.size),("full_axiom_walk",Json.arr audits),
      ("strict_delta_readbacks",toJson delta.size),("bridge_type_strict_equal",toJson true),
      ("retained_regions",toJson (regions.size+1)),("premise_changes",toJson (0 : Nat))]).pretty
  unless regions.size == 189 && readback.1.constants.size == 2 do throw (IO.userError "region owner")
  IO.println "PORT35_COMPLETE"
end Port35ANCHOR
run_cmd do
  let core ← Lean.MonadEnv.getEnv
  Lean.Elab.Command.liftIO (Port35ANCHOR.run core)

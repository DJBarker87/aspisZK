/- Copyright (c) 2023 Kim Morrison. All rights reserved.
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

open Lean
namespace Port32CONSUMER_Literal
-- Exact accepted Port18 helpers; readComplete is retained for copy assessment,
-- but streaming calls below own/free the complete region stack explicitly.
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
private def strictExpr (a b : Expr) : Bool := Id.run do
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


end Port32CONSUMER_Literal

namespace Port32CONSUMER_Select
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
  IO.println s!"PORT32_SELECTION names={selected.size} fresh={fresh.size} strict-core={reused.size}"
  return (fresh,selected,regions)
end Port32CONSUMER_Select

namespace Port32CONSUMER_Kernel
open Lean

namespace Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Environment
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
    replayConstants ((Port32CONSUMER_Select.dependencies ci).foldl (fun s n => s.insert n) ({} : NameSet))
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
    match (← get).env.toKernelEnv.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if !Port32CONSUMER_Literal.strictDeclaration (.ctorInfo info) (.ctorInfo info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.toKernelEnv.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !Port32CONSUMER_Literal.strictDeclaration (.recInfo info) (.recInfo info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end Replay

open Replay

/-- DISABLED candidate interface: caller must establish full exact-name closure,
complete groups and explicit origin policy before enabling this function.
"Replay" some constants into an `Environment`, sending them to the kernel for checking.

Throws a `IO.userError` if the kernel rejects a constant,
or if there are malformed recursors or constructors for inductive types.
-/
def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Environment) : IO Environment := do
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

end Port32CONSUMER_Kernel

macro:max x:term:max noWs "#usize" : term =>
  `(Aeneas.Std.Usize.ofNat $x (by decide))

def Port32CONSUMER_commandTexts : Array String := #[
  "set_option autoImplicit false",
  "noncomputable section",
  "open Aeneas Aeneas.Std Result",
  "open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep",
  "open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle",
  "namespace Port32CONSUMER",
  "open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared",
  "open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning",
  "open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation",
  "open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace",
  "open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd",
  "open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint",
  "open S2W_NativeConsolidation",
  "open AspisR1.S2W_D189Consolidation AspisR1.S2W_AuthenticatedInputs",
  "open AspisR1.S2W_InputSchedule AspisR1.S2W_ExpandedChildren AspisR1.S2W_TraceSplice",
  "open AspisR1.MultiproofConeCanonical",
  "theorem accepted_original_sdk_s2_s1 {W A E M Cv : Type} {N : Nat}\n    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)\n    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))\n    (std : TrustedStd copy) (allocator : Allocator A)\n    (e : Entry) (e2 : Entry) (world world2 : W)\n    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)\n    (admission2 : S2W_D189Consolidation.RuntimeEntrypointAdmission L e2 world2 7)\n    (adapterOps : AdapterRw.Ops) (ops : Ops)\n\n    (B : AspisR1PublicPreparation.FinishModel.Boundaries)\n    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)\n    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)\n    (extraction : S2W_DigestExtraction.AeneasExtraction\n      (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))\n      native1 native2 hashv)\n    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)\n    (sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)\n    (p1 : S2W_ExtractionBoundary.P1 sha256 H)\n    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)\n    (program : AdapterRw.solana_pubkey.Pubkey)\n    (data : Slice U8) (out : alloc.vec.Vec U8)\n    (initial final : A) (post : Heap (Nat → Record))\n    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =\n      ok (.Ok (out,post,final)))\n    (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)\n    (state2 final2 : A) (post2 : Heap (Nat → Record))\n    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =\n      ok (.Ok (post2,final2)))\n    (port : S2W_ExpandedChildren.ChildConeJoin E (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)))\n    (firstMarks : S2W_TraceSplice.FirstMarks port)\n    (secondMarks : S2W_TraceSplice.SecondMarks port) :\n    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧\n    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =\n      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧\n    ∃ (rawCut f : FirstCut) (s : SecondCut) selectedPublic outer pre middle fs ss,\n      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) e.first (e2.second secondSizes) out rawCut s ∧\n      f = (FirstCut.mk rawCut.proofAccount rawCut.publicAccount rawCut.raw rawCut.pub rawCut.statement selectedPublic rawCut.proof rawCut.split) ∧\n      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public\n        rawCut.statement = ok selectedPublic ∧\n      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) e.first (e2.second secondSizes) out f s ∧\n      (∃ encoded,\n        AspisS6CurrentCodecInstallation.decode f.pub = ok (.Ok f.statement) ∧\n        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 f.pub =\n          ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)) ∧\n        AspisS6CurrentCodecInstallation.encode f.statement = ok (.Ok encoded) ∧ encoded.val = f.pub.val ∧\n        f.split = AspisR1CurrentCaller.compact.SPLIT ∧\n        AspisR1CurrentCaller.FirstComposition.firstCurrent\n          AdapterRw.solana_program_error.ProgramError.InvalidAccountData (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)\n          (AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))))\n          (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error)) f.pub f.proof f.split = ok (.Ok out)) ∧\n      (f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧\n      payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 1))\n        (L.cellPayload world (L.accountData world 1)).descriptor.length =\n          MultiproofConeCanonical.bytesOf f.pub.val ∧\n      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual f.pub =\n        ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)) ∧\n      f.split=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)\n        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)\n        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)\n        (scratch : Array PE 29#usize),\n        AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1=ok (.Ok v) ∧\n        v.variant = .S2 ∧\n        (semanticBase ops B).op9 (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (FirstComposition.toCurrentPublic\n          (AspisR1PublicPreparation.PreparationBinding.preparationPublic (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))) v.semantic () none=ok (.Ok sem) ∧\n        AspisR1PublicPreparation.PreparedScratchModel.prepare\n          (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))\n          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) ()\n          (mapArray retainedE (Array.repeat 29#usize zero)) = ok (.Ok prepared,scratch) ∧\n        powersPublic 29#usize prepared.gamma = ok scratch ∧\n        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize (toClaimE prepared.gamma) = ok (mapArray toClaimE scratch) ∧\n        BorrowedClaimPrepared.claim (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (retainedSem sem) v.y1\n          (AspisR1SelectedWideViewV1.prepCarrier v.inactive) scratch prepared.kappa = ok (.Ok prepared.claim) ∧\n        AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧\n        AspisS1SemanticArrayRanges.CurrentVerifiedChallengesNumeric sem ∧\n        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧\n        OriginalPayloadClaimMeaning (retainedSem sem) v.y1\n          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))\n          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)\n          (mapArray toClaimE scratch) ∧\n        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,\n          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧\n          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧\n        ExactSerializedRankTrace (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) p f.pub root length\n          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧\n        Row31QueryProgramMeaning (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (AspisR1SelectedWideViewV1.preparedView v) prepared ∧\n        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) f.pub f.proof f.split () none\n          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out)) ∧\n      S2W_ExpandedTrace.runExpanded (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (children port)\n        (S2W_Observation.two (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) program e.first data (e2.second secondSizes) data2 slot) [] =\n        ok (.Ok out,S2W_ExpandedTrace.full (children port) outer) ∧\n      S2W_D189Interpretation.runOwned (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))\n        (S2W_Observation.two (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) program e.first data (e2.second secondSizes) data2 slot) [] e.heap =\n        ok (.Ok out,outer,e.heap) ∧\n      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧\n      post2 = e2.heap ∧\n      before e e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient ∧\n      before e e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 world2 e2.heap.ambient ∧\n      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),\n      CheckpointWriterConeJoin (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) decode H f.semantic f.pub f.proof f.split →\n      CheckpointReaderConeJoin (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) decode H s.pub s.proof s.checkpoint →\n      S2X.CheckpointVersionBinding\n        (payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →\n      P2Prime H f.proof f.pub s.proof s.pub →\n      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →\n      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →\n      S2W_ChildJoins.S8StageConeJoin f.proof y1 →\n      ∃ parsed,\n        S2W_LeadInterface.S2CallerFacts\n          (observation f s out nodes y1 pre middle fs ss (before e e2) (after e e2 post))\n          (S2Z.Oracle.leadDigest (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))) () H (bytesOf f.proof.val) (bytesOf f.pub.val)\n          (bytesOf out.val) parsed ∧\n        (∀ site, (observation f s out nodes y1 pre middle fs ss (before e e2) (after e e2 post)).reached site ↔\n          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by\n  let installed := (AspisS6CurrentFirstInstallation.install adapterOps\n        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))\n  have wrapped : S2W_D189Wrappers.first native1 copy allocator e program data initial =\n      ok (.Ok (out,post,final)) := by\n    rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]\n    exact accepted\n  obtain ⟨rawCut,s,outer,pre,middle,fs,ss,cuts,expanded,ownedFrame,layout,\n      unchanged,frame1,frame2,_oldConditional⟩ :=\n    S2W_D189Consolidation.accepted_run L sdk copy std allocator e e2 world world2\n      admission admission2 installed native1 native2 hashv extraction sha256 H p1 syscall\n      program data data2 slot initial state2 final final2 out post post2 wrapped accepted2\n      port firstMarks secondMarks\n  obtain ⟨written,frame,allS1⟩ :=\n    AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace\n      L sdk copy std allocator e world admission adapterOps ops B native1 native2 hashv extraction\n      p root length program data out initial final post accepted\n  obtain ⟨selectedPublic,selection,chosen,numeric⟩ :=\n    allS1 (e2.second secondSizes) rawCut s cuts\n  let f : FirstCut := (FirstCut.mk rawCut.proofAccount rawCut.publicAccount rawCut.raw rawCut.pub rawCut.statement selectedPublic rawCut.proof rawCut.split)\n  obtain ⟨_,_,allSdk⟩ := AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts\n    L sdk copy std allocator e world admission adapterOps\n    (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)\n    native1 native2 hashv extraction program data initial final out post accepted\n  obtain ⟨_,_,_,_,_,_,codec⟩ := allSdk (e2.second secondSizes) f s chosen\n  refine ⟨written,frame,rawCut,f,s,selectedPublic,outer,pre,middle,fs,ss,\n    cuts,rfl,selection,chosen,codec,numeric,expanded,ownedFrame,layout,\n    unchanged,frame1,frame2,?_⟩\n  intro decode nodes y1 writer reader history p2prime entry multiproof scan\n  obtain ⟨owned1,_⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator\n    e program data initial final out post wrapped\n  have source1 := (extraction.stage1 program e.first data).symm.trans owned1\n  have destinationSize := S2W_D189Entry.checkpoint_size e installed program data out source1\n  have versionAtWrite : S2X.CheckpointVersionBinding\n      (payloadBytes encode ((writeBracket e.heap 2 0 0 (source (nativeBytes out))).payload\n        (e.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) := by\n    rw [← written]; exact history\n  obtain ⟨_,⟨version⟩⟩ := returned_committed e.heap 2 0 0 out (bytesOf s.checkpoint.val)\n    rfl rfl destinationSize (writer.size out chosen.first) versionAtWrite\n  obtain ⟨parsed,partialFacts⟩ := S2W_InputSchedule.input_schedule installed H\n    e.first (e2.second secondSizes) f s out chosen decode nodes y1\n    writer reader version p2prime entry multiproof scan\n    (S2W_DigestExtraction.native_oracle installed native1 native2 hashv extraction sha256 H p1 syscall)\n    pre middle fs ss (S2W_D189Consolidation.before e e2) (S2W_D189Consolidation.after e e2 post)\n  have frames := S2W_D189Consolidation.wrapper_frames e e2 installed program data out source1 post written\n  refine ⟨parsed,?_,?_⟩\n  · apply (S2W_TwoFieldAudit.full_fields_iff _ installed H _ _ _ parsed partialFacts).2\n    exact ⟨fun site _ a allowed => frames.1 site a allowed,fun _ => frames.2⟩\n  · intro site\n    rw [layout]\n    rfl\n",
  "#print axioms accepted_original_sdk_s2_s1",
  "end Port32CONSUMER",
  "end",
  "set_option pp.all true in\n#print Port32CONSUMER.accepted_original_sdk_s2_s1",
  "#print axioms AspisR1.OraclePortCompactDraft.parse_header",
  "#print axioms AspisR1.S2W_D189Consolidation.accepted_run",
  "#print axioms AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace",
  "#print axioms AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts"
]

open Lean in
run_cmd do
  let env ← getEnv
  logInfo m!"PORT32_IMPORTS {env.header.modules.map (·.module)}"
  let (fresh,selected,regions) ← Port32CONSUMER_Select.load env
  let checked ← Port32CONSUMER_Kernel.replay fresh env
  setEnv checked
  for (n,c) in selected.toList do
    let some d := checked.toKernelEnv.find? n | throwError "missing checked {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do
      throwError "strict checked-CI/source readback failed {n}"
  logInfo m!"PORT32_FULL_STRICT_READBACK {selected.size}"
  -- Only namespace elaboration metadata is reconstructed; no logical declaration
  -- enters here. All constants already passed the ordinary kernel above.
  for (n,_) in selected.toList do
    let mut p := n.getPrefix
    while !p.isAnonymous do
      let ns := p
      modifyEnv (·.registerNamespace ns)
      p := p.getPrefix
  for text in Port32CONSUMER_commandTexts do
    let stx ← match Parser.runParserCategory (← getEnv) `command text "Port32CONSUMER_ComposedSource" with
      | .ok stx => pure stx
      | .error e => throwError "actual consumer source parse: {e}"
    Elab.Command.elabCommand stx
    if (← get).messages.hasErrors then throwError "actual consumer elaboration failed; no closure claim"
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
  for (n,c) in selected.toList do
    let some d := (← getEnv).toKernelEnv.find? n | throwError "missing final CI {n}"
    unless Port32CONSUMER_Literal.strictDeclaration c d do throwError "final CI drift {n}"
  -- The owner is used only AFTER every theorem/axioms/strict-CI audit. CompactedRegion
  -- has no destructor/finalizer; no buffer is freed when this command returns.
  -- These mappings and all borrowed references remain resident until OS process exit.
  unless regions.size > 0 do throwError "no retained regions"
  logInfo m!"PORT32_COMPLETE selected={selected.size} retained_regions={regions.size}"

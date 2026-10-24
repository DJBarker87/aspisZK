import Lean
open Lean
namespace Port29SDKDATA
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
private def strictDeclaration (a b : ConstantInfo) : Bool :=
  sameDeclaration a b && strictExpr a.type b.type && strictValue a b && strictRules a b
private def strictConstantVal (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && strictExpr a.type b.type

def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "empty module")
  pure data

private def owned (s : String) : String := String.ofList s.toList
private def ns (n : Name) : String := owned n.toString
private def emit (h : IO.FS.Handle) (j : Json) : IO Unit := h.putStrLn j.compress
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
private def deps (c : ConstantInfo) : Array String := Id.run do
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
  let mut out : Std.HashSet String := {}
  for n in ds do out := out.insert (ns n)
  return out.toArray
private def metadata (c : ConstantInfo) : Json :=
  match c with
  | .defnInfo v => toJson (v.all.toArray.map ns, toString (repr v.safety))
  | .thmInfo v => toJson (v.all.toArray.map ns)
  | .opaqueInfo v => toJson (v.all.toArray.map ns)
  | .inductInfo v => Json.arr #[toJson (v.all.toArray.map ns),toJson (v.ctors.toArray.map ns),
      toJson v.numParams,toJson v.numIndices,toJson v.numNested,toJson v.isRec,toJson v.isReflexive]
  | .ctorInfo v => toJson (ns v.induct,v.cidx,v.numParams,v.numFields)
  | .recInfo v => Json.arr #[toJson (v.all.toArray.map ns),toJson v.numParams,toJson v.numIndices,
      toJson v.numMotives,toJson v.numMinors,toJson v.k,
      toJson (v.rules.toArray.map (fun r => (ns r.ctor,r.nfields,r.rhs.getUsedConstants.map ns)))]
  | _ => Json.null
private def record (c : ConstantInfo) : Json := Json.mkObj [
  ("name",toJson (ns c.name)),("kind",toJson (kind c)),
  ("levels",toJson (c.levelParams.toArray.map ns)),("unsafe",toJson c.isUnsafe),
  ("partial",toJson c.isPartial),("has_value",toJson (c.hasValue (allowOpaque := true))),
  ("metadata",metadata c),("dependencies",toJson (deps c))]
private def readParts (p : System.FilePath) : IO (Array (ModuleData × CompactedRegion)) := do
  let mut ps := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then ps := ps.push q
  readModuleDataParts ps
private unsafe def indexOne (h : IO.FS.Handle) (side origin m p : String) : IO Unit := do
  let loaded ← readParts p
  let mut i := 0
  for (data,_) in loaded do
    emit h (Json.mkObj [("tag",toJson "part"),("side",toJson side),("origin",toJson origin),
      ("module",toJson m),("path",toJson p),("part",toJson i),
      ("constants",toJson data.constants.size),("names",toJson data.constNames.size),
      ("consistent",toJson (data.constNames == data.constants.map (·.name))),
      ("imports",toJson (data.imports.map (fun x => ns x.module))),
      ("extra",toJson data.extraConstNames.size),("entries",toJson data.entries.size)])
    for c in data.constants do
      emit h (Json.mkObj [("tag",toJson "constant"),("side",toJson side),("origin",toJson origin),
        ("module",toJson m),("path",toJson p),("part",toJson i),("constant",record c)])
    i := i + 1
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
private def rawCheck (d : ModuleData) : IO Unit := do
  unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
      d.constNames == d.constants.map (·.name) do
    throw (IO.userError "invalid raw transport header")
private unsafe def compareOne (h : IO.FS.Handle) (tag p q : String) (names : Array String) : IO Unit := do
  let a ← readParts p
  let b ← readParts q
  let sourcePart := ((tag.splitOn ":")[1]?).bind String.toNat?
  let some (da,_) := (if let some i := sourcePart then a.toList[i]? else a.toList.getLast?)
    | throw (IO.userError "empty left")
  let some (db,_) := b.toList.getLast? | throw (IO.userError "empty right")
  -- Original object comparisons are allowed only for incremental counterpart work.
  if tag != "full-original-current" && !tag.startsWith "source-readback:" then rawCheck da
  rawCheck db
  for n in names do
    let ca := da.constants.find? (fun c => ns c.name == n)
    let cb := db.constants.find? (fun c => ns c.name == n)
    match ca,cb with
    | some x,some y =>
      let same := sameDeclaration x y
      let exact := strictDeclaration x y
      let proofOnly := match x,y with
        | .thmInfo v,.thmInfo w => v.toConstantVal == w.toConstantVal && v.all == w.all
        | _,_ => false
      emit h (Json.mkObj [("tag",toJson tag),("name",toJson n),("left",toJson p),("right",toJson q),
        ("sameDeclaration",toJson same),("strict_v3",toJson exact),
        ("strict_type",toJson (strictConstantVal x y)),("strict_value",toJson (strictValue x y)),
        ("strict_rules",toJson (strictRules x y)),("same_constant_val",toJson (x.toConstantVal == y.toConstantVal)),
        ("same_value",toJson (x.value? (allowOpaque := true) == y.value? (allowOpaque := true))),
        ("proof_only_same_full_type",toJson (!same && proofOnly)),
        ("left_info",record x),("right_info",record y)])
    | _,_ => emit h (Json.mkObj [("tag",toJson tag),("name",toJson n),("left",toJson p),("right",toJson q),
        ("missing_left",toJson ca.isNone),("missing_right",toJson cb.isNone)])
  (b.map (·.2)).reverse.forM CompactedRegion.free
  (a.map (·.2)).reverse.forM CompactedRegion.free
private unsafe def exportOne (h : IO.FS.Handle) (side origin m p dest : String) (names : Array String) : IO Unit := do
  let loaded ← readParts p
  let mut wanted : Std.HashSet String := {}
  for n in names do wanted := wanted.insert n
  let mut i := 0
  for (data,_) in loaded do
    let cs := data.constants.filter (fun c => wanted.contains (ns c.name))
    unless cs.isEmpty do
      let path : System.FilePath := dest ++ "-part-" ++ toString i ++ ".olean"
      IO.FS.createDirAll path.parent.get!
      saveModuleData path m.toName { data with
        imports := #[]
        constants := cs
        constNames := cs.map (·.name)
        extraConstNames := #[]
        entries := #[] }
      -- New output audit, within the SAME diagnostic invocation: raw read only.
      let (check,region) ← readModuleData path
      rawCheck check
      unless check.constants.size == cs.size do throw (IO.userError "export count mismatch")
      for c in check.constants do
        let some original := cs.find? (fun x => x.name == c.name)
          | throw (IO.userError "export unexpected name")
        unless strictDeclaration original c do throw (IO.userError "export declaration mismatch")
      region.free
      emit h (Json.mkObj [("tag",toJson "transport"),("side",toJson side),("origin",toJson origin),
        ("module",toJson m),("source",toJson p),("path",toJson path.toString),("part",toJson i),
        ("names",toJson (cs.map (fun c => ns c.name)))])
    i := i + 1
  (loaded.map (·.2)).reverse.forM CompactedRegion.free
private unsafe def main : IO Unit := do
  let some dir ← IO.getEnv "PORT29_DATA" | throw (IO.userError "PORT29_DATA")
  let h ← IO.FS.Handle.mk (dir ++ "/Port29SDKDATA_raw.jsonl") .write
  let t := mkSort .zero
  let x := mkLambda `x .default t (mkBVar 0)
  let y := mkLambda `y .default t (mkBVar 0)
  let z := mkLambda `x .implicit t (mkBVar 0)
  let md1 : MData := ⟨[(`test, .ofNat 1)]⟩
  let md2 : MData := ⟨[(`test, .ofNat 2)]⟩
  let st1 : Syntax := .atom .none "x"
  let st2 : Syntax := .atom (.synthetic ⟨0⟩ ⟨1⟩ true) "x"
  let sm1 : MData := ⟨[(`syntax, .ofSyntax st1)]⟩
  let sm2 : MData := ⟨[(`syntax, .ofSyntax st2)]⟩
  for (label,a,b) in [("binder-name",x,y),("binder-annotation",x,z),
      ("metadata-value",mkMData md1 t,mkMData md2 t),
      ("metadata-syntax-source-info",mkMData sm1 t,mkMData sm2 t)] do
    emit h (Json.mkObj [("tag",toJson "api-counterexample"),("name",toJson label),
      ("alpha",toJson (a == b)),("expr_equal",toJson (Expr.equal a b)),
      ("strict_v3",toJson (strictExpr a b)),("reflexive",toJson (strictExpr a a))])
    if strictExpr a b || !strictExpr a a then throw (IO.userError "strict guard counterexample failed")
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_index.tsv") do
    if row.isEmpty then continue
    let [side,origin,m,p] := row.splitOn "\t" | throw (IO.userError "index row")
    indexOne h side origin m p
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_compare.tsv") do
    if row.isEmpty then continue
    let tag::p::q::names := row.splitOn "\t" | throw (IO.userError "compare row")
    compareOne h tag p q names.toArray
  h.flush
  if (← IO.getEnv "PORT29_INTERACTIVE") == some "1" then
    IO.FS.writeFile (dir ++ "/Port29SDKDATA_index-ready") "ready\n"
    let ready : System.FilePath := dir ++ "/Port29SDKDATA_export-ready"
    while !(← ready.pathExists) do IO.sleep 100
    for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_extra-compare.tsv") do
      if row.isEmpty then continue
      let tag::p::q::names := row.splitOn "\t" | throw (IO.userError "extra compare row")
      compareOne h tag p q names.toArray
  for row in ← IO.FS.lines (dir ++ "/Port29SDKDATA_export.tsv") do
    if row.isEmpty then continue
    let side::origin::m::p::dest::names := row.splitOn "\t" | throw (IO.userError "export row")
    exportOne h side origin m p dest names.toArray
  h.flush
  IO.println "Port29SDKDATA Strict-v3 diagnostic finished; axioms=N/A; no kernel insertion"
end Port29SDKDATA
#eval Port29SDKDATA.main

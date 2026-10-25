import Lean
open Lean
namespace Port31DATA355
-- EXACT Port29 guard span, only enclosing namespace differs.
-- Source74a62fd7b6, span SHA256 16430ef740da1dd737a1cce3806e6a2a1836e1d569a8971ac3ae75b598a6870e
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

private def owned (s : String) : String := String.ofList s.toList
private def ns (n : Name) : String := owned n.toString
-- Recursive constructor encoding, never printed-name parsing. Own String bytes.
private def en : Name → Json
  | .anonymous => Json.arr #[toJson "anon"]
  | .str p s => Json.arr #[toJson "str", en p, toJson (owned s)]
  | .num p i => Json.arr #[toJson "num", en p, toJson (toString i)]
private def emit (h : IO.FS.Handle) (j : Json) : IO Unit := h.putStrLn j.compress
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
-- FoldConsts intentionally omits projection structure names. Include them explicitly.
-- Expr hash/equality is used ONLY as a traversal cache, never variant selection.
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
private def deps (c : ConstantInfo) : Array Name := Id.run do
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
private def metadata (c : ConstantInfo) : Json :=
  match c with
  | .defnInfo v => toJson (v.all.toArray.map en, toString (repr v.safety))
  | .thmInfo v => toJson (v.all.toArray.map en)
  | .opaqueInfo v => toJson (v.all.toArray.map en)
  | .inductInfo v => Json.arr #[toJson (v.all.toArray.map en),toJson (v.ctors.toArray.map en),
      toJson v.numParams,toJson v.numIndices,toJson v.numNested,toJson v.isRec,toJson v.isReflexive]
  | .ctorInfo v => toJson (en v.induct,v.cidx,v.numParams,v.numFields)
  | .recInfo v => Json.arr #[toJson (v.all.toArray.map en),toJson v.numParams,toJson v.numIndices,
      toJson v.numMotives,toJson v.numMinors,toJson v.k,
      toJson (v.rules.toArray.map (fun r => (en r.ctor,r.nfields,(expressionDeps r.rhs).map en)))]
  | _ => Json.null
private def record (c : ConstantInfo) : Json := Json.mkObj [
  ("name",en c.name),("display",toJson (ns c.name)),("kind",toJson (kind c)),
  ("levels",toJson (c.levelParams.toArray.map en)),("unsafe",toJson c.isUnsafe),
  ("partial",toJson c.isPartial),("has_value",toJson (c.hasValue (allowOpaque := true))),
  ("metadata",metadata c),("dependencies",toJson ((deps c).map en)),
  ("logical_seed_rejected",toJson (c.isUnsafe || c.isPartial || match c with
    | .axiomInfo _ => c.name != `propext && c.name != `Classical.choice && c.name != `Quot.sound
    | _ => false))]
private def rawCheck (d : ModuleData) : IO Unit := do
  unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
      d.constNames == d.constants.map (·.name) do
    throw (IO.userError "invalid raw transport header")
-- Body and group serialization is exact raw DATA; no trusted module insertion.
-- Borrowed references stay inside this synchronous helper, which returns Unit.
private def readback (source : Array ConstantInfo) (check : ModuleData) : IO Unit := do
  rawCheck check
  unless check.constants.size == source.size do throw (IO.userError "export count")
  for i in [:source.size] do
    let some a := source[i]? | throw (IO.userError "source index")
    let some b := check.constants[i]? | throw (IO.userError "readback index")
    unless strictDeclaration a b do throw (IO.userError "strict source-part readback failed")
private unsafe def exportPart (h : IO.FS.Handle) (dir label : String) (d : ModuleData) : IO Unit := do
  let cs := if label.startsWith "BOOL:" then d.constants.filter (fun c => c.name == `Port31DATA.eq_true_of_not_eq_false) else d.constants
  let path : System.FilePath := dir ++ "/raw/" ++ label ++ ".olean"
  IO.FS.createDirAll path.parent.get!
  saveModuleData path `Port31DATA355.RawPayload { d with
    imports := #[]
    constants := cs
    constNames := cs.map (·.name)
    extraConstNames := #[]
    entries := #[] }
  let (check,region) ← readModuleData path
  readback cs check
  region.free
  emit h (Json.mkObj [("tag",toJson "export"),("origin",toJson label),
    ("path",toJson path.toString),("names",toJson (cs.map (fun c => en c.name))),
    ("strict_source_part_readback",toJson true)])
private def guardTests (h : IO.FS.Handle) : IO Unit := do
  let t := mkSort .zero
  let x := mkLambda `x .default t (mkBVar 0)
  let y := mkLambda `y .default t (mkBVar 0)
  let z := mkLambda `x .implicit t (mkBVar 0)
  let md1 : MData := ⟨[(`test, .ofNat 1)]⟩
  let md2 : MData := ⟨[(`test, .ofNat 2)]⟩
  let sm1 : MData := ⟨[(`syntax, .ofSyntax (.atom .none "x"))]⟩
  let sm2 : MData := ⟨[(`syntax, .ofSyntax (.atom (.synthetic ⟨0⟩ ⟨1⟩ true) "x"))]⟩
  let om1 : MData := ⟨[(`first, .ofNat 1),(`second, .ofNat 2)]⟩
  let om2 : MData := ⟨[(`second, .ofNat 2),(`first, .ofNat 1)]⟩
  for (label,a,b) in [("binder-name",x,y),("binder-annotation",x,z),
      ("metadata-value",mkMData md1 t,mkMData md2 t),
      ("syntax-source-info",mkMData sm1 t,mkMData sm2 t),
      ("ordered-metadata",mkMData om1 t,mkMData om2 t)] do
    emit h (Json.mkObj [("tag",toJson "guard"),("case",toJson label),
      ("alpha",toJson (a == b)),("expr_equal",toJson (Expr.equal a b)),
      ("strict",toJson (strictExpr a b)),("reflexive",toJson (strictExpr a a))])
    if strictExpr a b || !strictExpr a a then throw (IO.userError "strict guard test")
  let n := Name.num (.str .anonymous "test") 1
  let s := Name.str (.str .anonymous "test") "1"
  let d := Name.str .anonymous "test.1"
  if n == s || n == d || s == d then throw (IO.userError "Name guard")
  emit h (Json.mkObj [("tag",toJson "name-guard"),("names",toJson (#[n,s,d].map en))])
private def applications (h : IO.FS.Handle) (origin : String) (c : ConstantInfo) : IO Unit := do
  if c.name != `AspisR1.OraclePortCompactDraft.parse_header then return
  let some v := c.value? (allowOpaque := true) | return
  let mut todo := #[v]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.isApp && e.getAppFn.isConstOf `Bool.eq_true_of_not_eq_false then
      emit h (Json.mkObj [("tag",toJson "historical-bool-application"),("in",en c.name),("origin",toJson origin),
        ("arguments",toJson (e.getAppArgs.map (fun x => owned (toString (repr x))))),
        ("arg_count",toJson e.getAppArgs.size)])
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t v _ | .forallE _ t v _ => todo := (todo.push t).push v
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ v | .proj _ _ v => todo := todo.push v
    | _ => pure ()
private unsafe def analyze (h : IO.FS.Handle) (dir : String)
    (loaded : Array (String × ModuleData × CompactedRegion)) : IO Unit := do
  let mut candidates : Std.HashMap Name (Array (String × ConstantInfo)) := {}
  for (label,d,_) in loaded do
    unless d.constNames == d.constants.map (·.name) do throw (IO.userError "name inventory mismatch")
    if !(label.startsWith "S8:" || label.startsWith "BOOL:" || label.startsWith "CORE:") then rawCheck d
    emit h (Json.mkObj [("tag",toJson "part"),("origin",toJson label),
      ("names",toJson (d.constNames.map en)),("imports",toJson (d.imports.map (fun i => en i.module))),
      ("entries",toJson d.entries.size),("extra_names",toJson (d.extraConstNames.map en))])
    for c in d.constants do
      if label.startsWith "BOOL:" && c.name != `Port31DATA.eq_true_of_not_eq_false then continue
      candidates := candidates.insert c.name ((candidates[c.name]?.getD #[]).push (label,c))
      emit h (Json.mkObj [("tag",toJson "constant"),("origin",toJson label),("constant",record c)])
      applications h label c
      if label.startsWith "BOOL:" || c.name == `Bool.eq_true_of_not_eq_false then
        emit h (Json.mkObj [("tag",toJson "bool-body"),("origin",toJson label),("name",en c.name),
          ("type",toJson (owned (toString (repr c.type)))),
          ("value",toJson (owned (toString (repr (c.value? (allowOpaque := true))))))])
    if label.startsWith "S8:" || label.startsWith "BOOL:" || label.startsWith "CORE:" then exportPart h dir label d
  -- Presentation worklist selects endpoints only. The comparison key is the
  -- actual Name object; every matching additive-origin pair is retained.
  for row in ← IO.FS.lines (dir ++ "/Port31DATA_duplicates355.tsv") do
    let [id,display,leftMod,rightMod] := row.splitOn "\t"
      | throw (IO.userError "duplicate worklist row")
    let mut found := 0
    for (n,cs) in candidates.toArray do
      if ns n != display then continue
      for (a,x) in cs do
        if !a.startsWith "CURRENT:" || !a.endsWith (":" ++ leftMod ++ ":part0") then continue
        for (b,y) in cs do
          if !b.startsWith "CURRENT:" || !b.endsWith (":" ++ rightMod ++ ":part0") then continue
          unless x.name == y.name do throw (IO.userError "duplicate actual Name mismatch")
          found := found + 1
          emit h (Json.mkObj [("tag",toJson "owner43-pair"),("id",toJson id),
            ("name",en n),("left_name",en x.name),("right_name",en y.name),
            ("left",toJson a),("right",toJson b),("strict",toJson (strictDeclaration x y)),
            ("strict_type",toJson (strictConstantVal x y)),("strict_value",toJson (strictValue x y)),
            ("strict_rules",toJson (strictRules x y))])
    if found == 0 then throw (IO.userError ("uncovered duplicate pair " ++ id))
    emit h (Json.mkObj [("tag",toJson "owner43-covered"),("id",toJson id),("pairs",toJson found)])
  let roots := #[`AspisR1.S2W_D189Consolidation.accepted_run,
    `AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace,
    `AspisS6SdkSelectedSemanticCaller.original_sdk_selected_cuts]
  let mut todo := roots
  let mut seen : Std.HashSet Name := {}
  let mut gaps : Array Name := #[]
  let mut pairs := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let cs := candidates[n]?.getD #[]
    if cs.isEmpty then
      gaps := gaps.push n
      emit h (Json.mkObj [("tag",toJson "gap"),("name",en n),("display",toJson (ns n))])
      continue
    emit h (Json.mkObj [("tag",toJson "reached"),("name",en n),
      ("origins",toJson (cs.map (fun x => x.1)))])
    for (_,c) in cs do todo := todo ++ deps c
    for i in [:cs.size] do
      for j in [i+1:cs.size] do
        let some (a,x) := cs[i]? | throw (IO.userError "left index")
        let some (b,y) := cs[j]? | throw (IO.userError "right index")
        pairs := pairs + 1
        emit h (Json.mkObj [("tag",toJson "pair"),("name",en n),
          ("left",toJson a),("right",toJson b),("metadata",toJson (sameDeclaration x y)),
          ("strict",toJson (strictDeclaration x y)),("strict_type",toJson (strictConstantVal x y)),
          ("strict_value",toJson (strictValue x y)),("strict_rules",toJson (strictRules x y))])
  emit h (Json.mkObj [("tag",toJson "summary"),("roots",toJson (roots.map en)),
    ("reached",toJson seen.size),("known",toJson candidates.size),("gaps",toJson (gaps.map en)),
    ("pairs",toJson pairs),("kernel_ready",toJson false),("axioms",toJson "N/A: raw data only")])
private unsafe def main : IO Unit := do
  let some dir ← IO.getEnv "PORT31_DATA" | throw (IO.userError "PORT31_DATA")
  let h ← IO.FS.Handle.mk (dir ++ "/Port31DATA_raw355.jsonl") .write
  guardTests h
  let mut loaded : Array (String × ModuleData × CompactedRegion) := #[]
  for row in ← IO.FS.lines (dir ++ "/Port31DATA_inputs355.tsv") do
    let label::inputKind::paths := row.splitOn "\t" | throw (IO.userError "input group row")
    unless inputKind == "RAW" || inputKind == "OWN" || inputKind == "CORE" do
      throw (IO.userError "input group kind")
    if paths.isEmpty || (inputKind == "CORE" && paths.length != 3) then
      throw (IO.userError "input group parts")
    -- Core is EXACTLY one #[main,server,private] call. All part regions live
    -- through indexing, graph fixedpoint, export and strict source readback.
    let files : Array System.FilePath := paths.toArray.map (fun p => ⟨p⟩)
    let parts ← readModuleDataParts files
    unless parts.size == files.size do throw (IO.userError "group part count")
    emit h (Json.mkObj [("tag",toJson "group"),("origin",toJson label),
      ("kind",toJson inputKind),("paths",toJson paths),("parts",toJson parts.size)])
    let mut i := 0
    for (d,r) in parts do
      loaded := loaded.push (label ++ ":part" ++ toString i,d,r)
      i := i + 1
  analyze h dir loaded
  h.flush
  -- analyze has returned Unit: no graph/ConstantInfo/Expr/Syntax reference escapes.
  -- Retained part stack is freed in reverse, only after all synchronous use.
  (loaded.map (fun (_,_,r) => r)).reverse.forM CompactedRegion.free
  IO.println "Port31DATA raw diagnostic complete; axioms=N/A; no kernel insertion"
end Port31DATA355
#eval Port31DATA355.main

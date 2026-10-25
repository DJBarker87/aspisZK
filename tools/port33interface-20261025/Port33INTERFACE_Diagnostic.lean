import Lean
open Lean
namespace Port33INTERFACE
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

def encodeName : Name → Json
  | .anonymous => toJson (["anon"] : List String)
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson (String.ofList s.toList)]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

def inputs : Array (String × String × Array Name × String) := #[
("CURRENT:BASE:ExtractedOpeningQueriesModel:part0", "/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1/transport/ExtractedOpeningQueriesModel.olean", #[(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_2"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_22"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_32"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_11"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_31"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_4"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_19"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_15"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_27"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_17"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "Boundaries"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "Boundaries") "rec"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "Boundaries") "mk"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_25"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_24"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "Boundaries") "embed"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_5"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_29"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_23"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_18"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_3"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_28"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_7"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_6"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_16"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_10"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_9"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_8"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_1"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "match_1"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_12"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_30"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_13"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_26"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_20"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_14"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "queries") "_proof_21"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "QueriesModel") "Boundaries") "decode")], "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part0.olean"),
("CURRENT:INCREMENTAL:Query31ArrayReadback:part0", "/private/tmp/s126-sdk-current-incremental-release-20261024-v1/transport/Query31ArrayReadback.olean", #[(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "update_readback"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "index_mut_readback"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "update_readback_other")], "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part1.olean"),
("CURRENT:INCREMENTAL:Query31DigestInputBridge:part0", "/private/tmp/s126-sdk-current-incremental-release-20261024-v1/transport/Query31DigestInputBridge.olean", #[(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "digestCall_input_eq_readParts")], "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part2.olean"),
("CURRENT:INCREMENTAL:Query31SourceCalls:part0", "/private/tmp/s126-sdk-current-incremental-release-20261024-v1/transport/Query31SourceCalls.olean", #[(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "squeeze"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "mk"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "state"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "mk"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "rec"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "tag"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "rec"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "state"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "hadvanceTag"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "advance"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "hadvanceState"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "hdigest"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "output"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "input"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestCall") "casesOn"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "hsqueezeTag"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "DigestPair") "hsqueezeState"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "stateChain"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "stateChain") "_f"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "stateChain") "match_1"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "queries_success_with_digest_pairs_full"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_four"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "index8"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "small_nat_usize"),(Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "small_nat_usize") "_proof_1_2"),(Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "small_nat_usize") "_proof_1_1"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_two"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "stateChain") "_proof_1"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "bind_success"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_one"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_zero"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "queries_success_with_digest_pairs_full") "_proof_1_8"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_three"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_six"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "materializedOutputs"),(Name.str (Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "materializedOutputs") "_proof_1"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_five"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "index8_seven"),(Name.str (Name.str (Name.str (Name.num (Name.str (Name.str Name.anonymous "_private") "Query31SourceCalls") 0) "AspisR1PublicPreparation") "Query31SourceSchedule") "pair_bind_success")], "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part3.olean"),
("CURRENT:INCREMENTAL:Query31SourceOracleBridge:part0", "/private/tmp/s126-sdk-current-incremental-release-20261024-v1/transport/Query31SourceOracleBridge.olean", #[(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "queries_success_pairs_functional_full"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "digestPair_functional"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "advance_call_functional"),(Name.str (Name.str (Name.str Name.anonymous "AspisR1PublicPreparation") "Query31SourceSchedule") "squeeze_call_functional")], "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-part4.olean"),
]

def runDiagnostic : IO Unit := do
  IO.FS.createDirAll "/private/tmp/Port33INTERFACE-20261025"
  let mut regions : Array (ModuleData × CompactedRegion) := #[]
  let mut variants : Array (String × ConstantInfo) := #[]
  let mut reports : Array Json := #[]
  for (origin,path,names,output) in inputs do
    let part ← readModuleData ⟨path⟩
    regions := regions.push part
    let d := part.1
    unless d.imports.isEmpty && d.extraConstNames.isEmpty && d.entries.isEmpty &&
        d.constNames == d.constants.map (·.name) do
      throw (IO.userError "input is not complete raw DATA")
    let cs := d.constants.filter (fun c => names.contains c.name)
    unless cs.size == names.size do throw (IO.userError "missing exact-name variant")
    saveModuleData ⟨output⟩ `Port33INTERFACE.RawPayload {
      isModule := false, imports := #[], constNames := cs.map (·.name),
      constants := cs, extraConstNames := #[], entries := #[] }
    let check ← readModuleData ⟨output⟩
    regions := regions.push check
    unless check.1.imports.isEmpty && check.1.extraConstNames.isEmpty &&
        check.1.entries.isEmpty && check.1.constNames == cs.map (·.name) &&
        check.1.constants.size == cs.size do throw (IO.userError "raw readback header")
    for i in [:cs.size] do
      let c := cs[i]!
      unless strictDeclaration c check.1.constants[i]! do
        throw (IO.userError "strict source-part CI readback")
      variants := variants.push (origin,c)
      reports := reports.push (Json.mkObj [
        ("origin",toJson origin),("name",encodeName c.name),
        ("levels",toJson (c.levelParams.map encodeName)),
        ("type_rendering",toJson (toString c.type)),
        ("value_rendering",toJson (c.value? (allowOpaque := true) |>.map toString)),
        ("raw_output",toJson output),("raw_index",toJson i),
        ("strict_complete_CI_readback",toJson true),
        ("logical_validation",toJson "NONE: raw DATA")])
  let mut comparisons : Array Json := #[]
  for i in [:variants.size] do
    for j in [i+1:variants.size] do
      let (o,c) := variants[i]!
      let (p,d) := variants[j]!
      if c.name == d.name then
        comparisons := comparisons.push (Json.mkObj [
          ("name",encodeName c.name),("left",toJson o),("right",toJson p),
          ("strict_type",toJson (strictExpr c.type d.type)),
          ("strict_value",toJson (strictValue c d)),
          ("strict_CI",toJson (strictDeclaration c d))])
  IO.FS.writeFile "/private/tmp/Port33INTERFACE-20261025/Port33INTERFACE-diagnostic.json"
    (Json.pretty (Json.mkObj [("variants",Json.arr reports),("comparisons",Json.arr comparisons)]))
  unless regions.size == 2 * inputs.size do throw (IO.userError "region lifetime owner")
  IO.println s!"PORT33_RAW_COMPLETE variants={variants.size} regions={regions.size}; raw IO axioms N/A"

-- Normal checked, tiny synthetic declarations. No raw project CI enters the kernel.
run_cmd do
  let original ← Lean.getEnv
  let mut k := original.toKernelEnv
  let names := #[`_private.Port33INTERFACE_Left.0.Port33INTERFACE.collision,
                 `_private.Port33INTERFACE_Right.0.Port33INTERFACE.collision]
  unless names[0]! != names[1]! &&
      privateToUserName names[0]! == privateToUserName names[1]! do
    throwError "synthetic collision names do not share a normalized name"
  for n in names do
    let d := Declaration.thmDecl {
      name := n, levelParams := [], type := mkConst ``True,
      value := mkConst ``True.intro }
    match k.addDeclCore 0 d (cancelTk? := none) with
    | .error ex => throwError "{← ex.toMessageData {} |>.toString}"
    | .ok next => k := next
  for n in names do
    let some c := k.find? n | throwError "kernel exact-name lookup failed"
    unless strictExpr c.type (mkConst ``True) &&
        c.value? (allowOpaque := true) == some (mkConst ``True.intro) do
      throwError "synthetic strict CI readback failed"
  let temporary := Environment.ofKernelEnv k
  for n in names do
    logInfo m!"PORT33_SYNTHETIC {n}: kernel={((k.find? n).isSome)} temporaryElab={((temporary.find? n).isSome)}"
  let mut todo := names
  let mut seen : NameSet := {}
  let mut leaves : Array Name := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := k.find? n | throwError "missing synthetic audit dependency {n}"
    if c.isUnsafe || c.isPartial then throwError "inadmissible synthetic dependency {n}"
    if c.isAxiom then leaves := leaves.push n
    logInfo m!"PORT33_SYNTHETIC axiom-walk node {n}"
    todo := todo ++ c.getUsedConstantsAsSet.toList.toArray
  unless leaves.isEmpty do throwError "unexpected synthetic axioms {leaves}"
  logInfo m!"PORT33_SYNTHETIC complete kernel axiom dependency walk leaves={leaves}; synthetic only, no original body identity"
  -- Temporary kernel context is never installed into elaboration.
  liftIO runDiagnostic
  logInfo "PORT33_COMPLETE diagnostic and synthetic only; no Query31 theorem checked"
end Port33INTERFACE

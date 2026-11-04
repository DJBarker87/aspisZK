import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command
namespace NER
/-- Include recursor reduction rules and constant-name metadata, not only values. -/
def referenceNames (c : ConstantInfo) : Array Name := Id.run do
 let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
 match c with
 | .defnInfo v => refs := refs ++ v.all.toArray
 | .thmInfo v => refs := refs ++ v.all.toArray
 | .opaqueInfo v => refs := refs ++ v.all.toArray
 | .inductInfo v => refs := refs ++ v.ctors.toArray ++ v.all.toArray
 | .ctorInfo v => refs := refs.push v.induct
 | .recInfo v =>
  refs := refs ++ v.all.toArray
  for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
 | _ => pure ()
 return refs
/-- Same stable first-occurrence projection as NER_ModuleTables.inspect. -/
def canonicalImports (xs : Array String) : Array String := Id.run do
 let mut result := #[]
 for x in xs do
  if !result.contains x then result := result.push x
 return result
def importsMatch (actual expected : Array String) : Bool := canonicalImports actual == expected
/-- Serialized module tables also carry reproducible theorem-cache entries.
Compare their complete declaration shape; theorem proofs are irrelevant only
when their types, levels and mutual metadata agree structurally. -/
def quotTag : QuotKind → Nat
 | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
def sameDeclaration (a b : ConstantInfo) : Bool :=
 match a,b with
 | .axiomInfo x,.axiomInfo y => x == y
 | .defnInfo x,.defnInfo y => x == y
 | .thmInfo x,.thmInfo y => x.toConstantVal == y.toConstantVal && x.all == y.all
 | .opaqueInfo x,.opaqueInfo y => x == y
 | .ctorInfo x,.ctorInfo y => x == y
 | .recInfo x,.recInfo y => x == y
 | .quotInfo x,.quotInfo y => x.toConstantVal == y.toConstantVal && quotTag x.kind == quotTag y.kind
 | .inductInfo x,.inductInfo y =>
   x.toConstantVal == y.toConstantVal && x.numParams == y.numParams &&
   x.numIndices == y.numIndices && x.all == y.all && x.ctors == y.ctors &&
   x.numNested == y.numNested && x.isRec == y.isRec && x.isUnsafe == y.isUnsafe &&
   x.isReflexive == y.isReflexive
 | _,_ => false
/-- Inspect each module's own declarations against the checked private environment. -/
def loadedScan (env : Environment) (output : System.FilePath)
    (expected : Std.HashMap String (Array String)) : IO Bool := do
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk output .write
 let mut failed := false
 let mut owners : Std.HashMap Name Name := {}
 for h : idx in [0:env.header.moduleNames.size] do
  let n := env.header.moduleNames[idx]
  let data := env.header.moduleData[idx]!
  let mut dangling : Array Json := #[]
  let mut duplicateOwners : Array Json := #[]
  let mut cachedReplicas : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   let some c := env.checked.get.find? declared.name | do
    dangling := dangling.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString),("phase",toJson "own_declaration")])
    continue
   if let some prior := owners[declared.name]? then
    let row := Json.mkObj [("name",toJson declared.name.toString),("previous",toJson prior.toString),("current",toJson n.toString),
      ("proof_identical",toJson (declared.value? true == c.value? true))]
    if sameDeclaration declared c then cachedReplicas := cachedReplicas.push row
    else duplicateOwners := duplicateOwners.push row
   else if !sameDeclaration declared c then
    duplicateOwners := duplicateOwners.push (Json.mkObj [("name",toJson declared.name.toString),("current",toJson n.toString),("reason",toJson "serialized declaration differs from selected owner")])
   owners := owners.insert declared.name n
   let refs := referenceNames c
   for dep in refs do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     dangling := dangling.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  let loaderImports := data.imports.map (fun i => i.module.toString)
  let imports := canonicalImports loaderImports
  let importMatch := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !duplicateOwners.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("loader_imports",toJson loaderImports), ("imports_match",toJson importMatch), ("dangling",toJson dangling), ("duplicate_owners",toJson duplicateOwners), ("cached_replicas",toJson cachedReplicas),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NER

/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) :=
    if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else if mode == "scan" then (#[`NGA_COMBINED_IMPORT], #[])
    else if mode == "proof0" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Cache.prelude_source, `NGA_CacheDomain.row_bounded, `NGA_CacheDomain.prepared_bounded, `NGA_CacheDomain.source, `NGA_Cell.get_set])
    else if mode == "proof1" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Cell.index, `NGA_Step.bounded_get, `NGA_Step.source, `NGA_Nine.loop, `NGA_Nine.trace_nodup])
    else if mode == "proof2" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Nine.trace_complete, `NGA_Nine.source, `NGA_Small.product_bound, `NGA_Small.loop, `NGA_Small.zero_value])
    else if mode == "proof3" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Small.source, `NGA_PreparePairs.source, `NGA_PreparePairs.same_run, `NGA_SmallResult.source, `NGA_Wrappers.domain])
    else if mode == "proof4" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Wrappers.source, `NGA_Wrappers.two, `NGA_Wrappers.three, `NGA_Wrappers.four, `NGA_NativeOps.cm_square_total])
    else if mode == "proof5" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_NativeOps.qm_square_total, `NGA_NativeOps.product, `NGA_NativeOps.square, `NGA_NativeOps.mul_u, `NGA_NativeOps.addition])
    else if mode == "proof6" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_CanonicalInjective.word, `NGA_CanonicalInjective.qm, `NGA_CanonicalInjective.wide, `NGA_WideSquare.value, `NGA_WideSquare.source])
    else if mode == "proof7" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_Converter.value, `NGA_ChannelAlgebra.row_add, `NGA_ChannelAlgebra.add, `NGA_ChannelAlgebra.zero, `NGA_ChannelAlgebra.row_product])
    else if mode == "proof8" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_ChannelAlgebra.product, `NGA_CacheValues.source, `NGA_Accumulate.source, `NGA_SumAlgebra.channels, `NGA_SumAlgebra.source])
    else if mode == "proof9" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_WrapperValues.source, `NGA_WrapperValues.two, `NGA_WrapperValues.three, `NGA_WrapperValues.four, `NGA_ArrayExt.row_eq])
    else if mode == "proof10" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_ArrayExt.source, `NGA_OuterStep.source, `NGA_Indexed.same_inputs, `NGA_Indexed.full_value, `NGA_SquareCallees.product])
    else if mode == "proof11" then
      (#[`NGA_COMBINED_IMPORT], #[`NGA_SquareCallees.square, `NGA_SquareCallees.addition, `NGA_SquareCallees.mulU_words, `AspisR1.RPx_Deployed.deployed])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NGA_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NGA_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFN_SCAN_FAILED" else "NFN_SCAN_ZERO_DANGLING")
    return if failed then 1 else 0
  let ctx : Command.Context := {
    fileName := "NEP_Driver"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  let action : CommandElabM Bool := do
    let mut failed := false
    for root in roots do
      try
        elabCommand (← `(command| #print axioms $(mkIdent root)))
        NEP.audit root ("NEP_" ++ mode ++ "_" ++ root.toString)
      catch e =>
        logError e.toMessageData
        failed := true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0

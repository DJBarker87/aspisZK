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
    if mode == "proof0" then
      (#[`NFN_COMBINED_IMPORT], #[`NFN_NFB_GeometryComposed.result_state_effects, `NFN_NFB_GeometryComposed.accepted_physical, `NFN_NFB_GeometryInstall.standard])
    else if mode == "proof1" then
      (#[`NFN_COMBINED_IMPORT], #[`NFN_NFB_GeometryInstall.step, `NFN_NFB_GeometryInstall.loop, `NFN_NEW_GeometryComplete.complete])
    else if mode == "proof2" then
      (#[`NFN_COMBINED_IMPORT], #[`NFN_PhaseTransport.legacy_roundtrip, `NFN_PhaseTransport.owner_roundtrip, `NFN_PhaseTransport.observer_none])
    else if mode == "proof3" then
      (#[`NFN_COMBINED_IMPORT], #[`NFN_PhaseTransport.observer_some, `NFN_ReserveOwner.error_owner, `AspisR1.NFG_ProductOk.result])
    else if mode == "proof4" then
      (#[`NFN_COMBINED_IMPORT], #[`AspisR1.NFG_PushRoot.private_result, `AspisR1.NFG_PushRoot.public_result, `AspisR1.NFG_PushRoot.private_domains])
    else if mode == "proof5" then
      (#[`NFN_COMBINED_IMPORT], #[`AspisR1.NFG_SmallEffects.neg, `AspisR1.NFG_SmallEffects.zero, `NFG_InverseZeroDomain.unique])
    else if mode == "proof6" then
      (#[`NFN_COMBINED_IMPORT], #[`NFG_InversePanic.zero, `AspisR1.RPx_Deployed.deployed])
    else if mode == "queryproof0" then
      (#[`NFN_QueryModel], #[`NFN_QueryModel.root, `NFN_QueryModel.geometry_then_query, `NFN_QueryModel.result_state_effects])
    else if mode == "queryproof1" then
      (#[`NFN_QueryModel], #[`NFN_QueryModel.progress, `NFN_QueryModel.fuel22_budget])
    else if mode == "queryscan" then (#[`NFN_QueryModel], #[])
    else if mode == "scan" then (#[`NFN_COMBINED_IMPORT], #[])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NFN_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NFN_LOADED_scan.jsonl") expected
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

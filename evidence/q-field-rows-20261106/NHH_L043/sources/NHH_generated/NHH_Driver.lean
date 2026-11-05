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
    else if mode == "scan" then (#[`NHH_COMBINED_IMPORT], #[])
    else if mode == "proof0" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_Embedding.base, `NHH_Embedding.inherent, `NHH_Embedding.complex, `NHH_Embedding.quadratic, `NHH_Embedding.wide, `NHH_Embedding.word_spec, `NHH_Embedding.canonical, `NHH_Embedding.same_canonical_word, `NHH_Embedding.accumulation, `NHH_BaseOps.mul_probe])
    else if mode == "proof1" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_BaseOps.mul_native, `NHH_BaseOps.mul_value, `NHH_BaseOps.square_body, `NHH_BaseOps.square_chain, `NHH_BaseOps.inverse_chain, `NHH_ScalarDomain.add_probe, `NHH_ScalarDomain.addition, `NHH_ScalarDomain.inverse_probe, `NHH_ScalarDomain.inverse_total, `NHH_ScalarDomain.inverse_zero])
    else if mode == "proof2" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_ScalarDomain.norm, `NHH_EncodedScalar.multiply, `NHH_EncodedScalar.addition, `NHH_EncodedScalar.negation, `NHH_EncodedScalar.inverse, `NHH_CMInverse.roundtrip, `NHH_CMInverse.fixed, `NHH_CMInverse.zero, `NHH_CMInverse.encoded_association, `NHH_CMInverse.canonical_association])
    else if mode == "proof3" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_CMTrace.source, `NHH_CMTrace.encoded, `NHH_CMTrace.backend_domain, `NHH_CMSampler.narrow_roundtrip, `NHH_CMSampler.raw_product, `NHH_CMSampler.scalar_add, `NHH_CMSampler.scalar_sub, `NHH_CMSampler.scalar_neg, `NHH_CMSampler.scalar_reduce, `NHH_CMSampler.scalar_double])
    else if mode == "proof4" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_CMSampler.scalar_multiply, `NHH_CMSampler.add_association, `NHH_CMSampler.sub_association, `NHH_CMSampler.neg_association, `NHH_CMSampler.mul_association, `NHH_CMSampler.square_association, `NHH_CMSampler.rotate_association, `NHH_CMAlgebra.injective, `NHH_CMAlgebra.unmap, `NHH_CMAlgebra.addition])
    else if mode == "proof5" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_CMAlgebra.subtraction, `NHH_CMAlgebra.negation, `NHH_CMAlgebra.multiply, `NHH_CMAlgebra.square, `NHH_CMAlgebra.rotate, `NHH_CMBridge.decode_live, `NHH_CMBridge.encoded_canonical, `NHH_CMBridge.packet, `NHH_CMBridge.selected_backend, `NHH_CMBridge.specialized_packet])
    else if mode == "proof6" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_AllScalar.multiply, `NHH_AllScalar.body, `NHH_AllScalar.square, `NHH_AllScalar.inverse, `NHH_CMAll.from_to, `NHH_CMAll.to_from, `NHH_CMAll.pullback, `NHH_CMAll.inv_with, `NHH_CMAll.inverse_association, `NHH_CMAll.mul_association])
    else if mode == "proof7" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_CMAll.square_association, `NHH_CMAll.inverse_result, `NHH_CMAll.mul_result, `NHH_CMAll.square_result, `NHH_CMAll.sub_result, `NHH_CMAll.neg_result, `NHH_CMAll.rotate_result, `NHH_QInverse.roundtrip, `NHH_QInverse.canonical, `NHH_QInverse.test_association])
    else if mode == "proof8" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_QInverse.zero_test, `NHH_QInverse.try_nonzero, `NHH_QInverse.try_zero, `NHH_QInverse.inverse_nonzero, `NHH_QInverse.inverse_zero, `NHH_QInverse.try_association, `NHH_QInverse.canonical_try_association, `NHH_QAll.from_to, `NHH_QAll.to_from, `NHH_QAll.try_association])
    else if mode == "proof9" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_QAll.try_result, `NHH_QAll.inverse_association, `NHH_QTrace.source, `NHH_QTrace.encoded, `NHH_QTrace.zero, `NHH_QTrace.inverse_domain, `NHH_QBridge.decode_live, `NHH_QBridge.try_packet, `NHH_QBridge.inverse_packet, `NHH_QNeg.cm_result])
    else if mode == "proof10" then
      (#[`NHH_COMBINED_IMPORT], #[`NHH_QNeg.cm_encode, `NHH_QNeg.result, `NHH_QNeg.coordinates, `NHH_QNeg.q_injective, `NHH_QNeg.roundtrip, `NHH_QNeg.canonical_result, `NHH_StubDomains.scalar_canonical, `NHH_StubDomains.cm_log, `NHH_StubDomains.qm_log, `AspisR1.RPx_Deployed.deployed])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NHH_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NHH_LOADED_scan.jsonl") expected
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

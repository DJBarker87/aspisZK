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
/-- Inspect each module's own declarations against the checked private environment. -/
def loadedScan (env : Environment) (output : System.FilePath)
    (expected : Std.HashMap String (Array String)) : IO Bool := do
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk output .write
 let mut failed := false
 for h : idx in [0:env.header.moduleNames.size] do
  let n := env.header.moduleNames[idx]
  let data := env.header.moduleData[idx]!
  let mut dangling : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   let some c := env.checked.get.find? declared.name | do
    dangling := dangling.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString),("phase",toJson "own_declaration")])
    continue
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
  if !dangling.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("loader_imports",toJson loaderImports), ("imports_match",toJson importMatch), ("dangling",toJson dangling),
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
      (#[`NGD_COMBINED_IMPORT], #[`NGD_SlotModel.reference, `NGD_SlotPanic.rejected, `NGD_ErrorPort.to_from, `NGD_ErrorPort.from_to, `NGD_ErrorPort.result_roundtrip, `NGD_ParseCut.emitted, `NGD_AtShape.reference, `NGD_QDecodeLaw.stub_law, `NGD_DecodeGuards.invalid_row, `NGD_DecodeGuards.offset_overflow, `NGD_DecodeGuards.length_overflow, `NGD_DecodeGuards.end_overflow])
    else if mode == "proof1" then
      (#[`NGD_COMBINED_IMPORT], #[`NGD_DecodeGuards.range_error, `NGD_SemanticSchedule.start, `NGD_SemanticSchedule.finish, `NGD_SemanticSchedule.advance, `NGD_SemanticSchedule.windows, `NGD_SemanticSchedule.expansion_domain, `NGD_SemanticSchedule.dst_mono, `NGD_SemanticSchedule.src_mono, `NGD_SemanticSchedule.disjoint, `NGD_SemanticSchedule.input_disjoint, `NGD_ParseReference.invalid_cut, `NGD_ParseReference.shape_total])
    else if mode == "proof2" then
      (#[`NGD_COMBINED_IMPORT], #[`NGD_ParseReference.all_inputs, `NGD_ParseReference.map_bind, `NGD_ParseReference.map_ok, `NGD_ParseReference.map_fail, `NGD_ParseReference.map_div, `NGD_ParseReference.map_if, `NGD_ParseReference.wrap_checked, `NGD_ParseReference.framed_cut, `NGD_AtCut.emitted, `NGD_AtReference.forward, `NGD_DecodeGeometry.fitting, `NGD_DecodeGeometry.selected_low])
    else if mode == "proof3" then
      (#[`NGD_COMBINED_IMPORT], #[`NGD_DecodeGeometry.framed_low, `NGD_DecodeGeometry.low_length, `NGD_RowPayload.row_cases, `NGD_RowPayload.present, `NGD_RowPayload.exact_size, `NGD_RowPayload.compact_shape, `NGD_RowPayload.cursor_bound, `NGD_DecodeValueTotal.q_parser_spec, `NGD_DecodeValueTotal.payload_spec, `NGD_DecodeValueTotal.value_total, `NGD_AtDomains.from_cursor, `NGD_DecodeValueLaw.value])
    else if mode == "proof4" then
      (#[`NGD_COMBINED_IMPORT], #[`NGD_DecodeTrace.step, `NGD_DecodeTrace.loop, `NGD_DecodeEntry.ready, `NGD_WrapFacts.add, `NGD_WrapFacts.mul, `NGD_SlotBoundaries.step0, `NGD_SlotBoundaries.step1, `NGD_SlotBoundaries.step2, `NGD_SlotBoundaries.step3, `NGD_SlotBoundaries.step4, `NGD_SlotBoundaries.step5, `NGD_SlotBoundaries.boundary0])
    else if mode == "proof5" then
      (#[`NGD_COMBINED_IMPORT], #[`NGD_SlotBoundaries.boundary1, `NGD_SlotBoundaries.boundary2, `NGD_SlotBoundaries.boundary3, `NGD_SlotBoundaries.boundary4, `NGD_SlotBoundaries.boundary5, `NGD_SlotBoundaries.boundary6, `AspisR1.RPx_Deployed.deployed])
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
    for line in ← IO.FS.lines (if mode == "queryscan" then "NGD_QUERY_EXPECTED_IMPORTS.jsonl" else "NGD_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NGD_QUERY_LOADED_scan.jsonl" else "NGD_LOADED_scan.jsonl") expected
    IO.println (if failed then "NGD_SCAN_FAILED" else "NGD_SCAN_ZERO_DANGLING")
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

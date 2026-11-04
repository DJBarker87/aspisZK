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
      (#[`NFT_STAGE2_IMPORT], #[`NFT_Bytes.cm_frame, `NFT_Square.source, `NFT_Square.wide_product, `NFT_Square.scalar_product, `NFT_Square.generated_scalar_product])
    else if mode == "proof1" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_Bytes.qm_frame, `NFT_NegWord.wrapping_value, `NFT_NegWord.source, `NFT_NegSub.scalar, `NFT_WideNeg.scalar])
    else if mode == "proof2" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_WideNeg.source, `NFT_Karatsuba.source, `NFT_Karatsuba.total, `NFT_Karatsuba.mul_r_eq_hiding, `NFT_Karatsuba.mul_r_value])
    else if mode == "proof3" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_PackPrefix.source, `NFT_ZeroPhysical.pad_length, `NFT_ZeroPhysical.take_append_bounded, `NFT_ZeroPhysical.window_pad, `NFT_ZeroPhysical.suffix_pad])
    else if mode == "proof4" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_ZeroPhysical.pointer_step, `NFT_ZeroPhysical.slice_step, `NFT_ZeroPhysical.length_step, `NFT_ZeroPhysical.frame, `NFT_ZeroPhysical.physical_view])
    else if mode == "proof5" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_Cmr.source, `NFT_Cmr.double_value, `NFT_Cmr.sub_value, `NFT_Cmr.add_value, `NFT_ChannelModel.product_bound])
    else if mode == "proof6" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_ChannelModel.addition_bound, `NFT_ChannelModel.selected, `NFT_ChannelModel.frame, `NFT_ChannelModel.control, `NFT_ChannelModel.complete])
    else if mode == "proof7" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_Pack.graph, `NFT_Pack.padded_length, `NFT_Pack.padded_canonical, `NFT_Pack.source, `NFT_PackWords.tail])
    else if mode == "proof8" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_PackWords.source, `NFT_ZeroJoin.source_and_frame, `NFT_ZeroJoin.checkpoint_bound, `NFT_Dot.scalar_product, `NFT_Dot.control])
    else if mode == "proof9" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_PreparedSum3.source, `NFT_PreparedSum3.constructor_domain, `AspisR1PoseidonPreparedChannelRunStepLocal.runStep_success, `AspisR1PoseidonPreparedChannelLoopExact.loop_success_fuel, `NFT_PreparedFrame.frame])
    else if mode == "proof10" then
      (#[`NFT_STAGE2_IMPORT], #[`NFT_PreparedFrame.control, `NFT_ChannelFour.generated_step, `NFT_DotSource.source, `NFT_DotSource.caller_rows, `AspisR1.FJh_M31DotInput.source_success])
    else if mode == "proof11" then
      (#[`NFT_STAGE2_IMPORT], #[`AspisR1.FJh_M31DotChunkModel.loop_success_fuel, `NFT_FieldFrontier.products_bound, `NFT_FieldFrontier.four_fit])
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
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFQ_QUERY_EXPECTED_IMPORTS.jsonl" else "NFQ_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env (if mode == "queryscan" then "NFQ_QUERY_LOADED_scan.jsonl" else "NFQ_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFQ_SCAN_FAILED" else "NFQ_SCAN_ZERO_DANGLING")
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

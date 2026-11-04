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
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.product_bound, `AspisR1.NFF_QueryProduct.emitted, `AspisR1.NFI_InnerCut.same_input, `AspisR1.NFI_TraceResult.erase_pure])
    else if mode == "proof1" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedOuterLoop.replay, `AspisR1.NFF_FullWrapper.replay, `AspisR1.NFI_InnerCut.erased, `AspisR1.NFI_TraceResult.fail_prefix])
    else if mode == "proof2" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_RawLog.same_log, `AspisR1.NFF_LoggedStep.active, `AspisR1.NFI_InnerTrace.replay, `AspisR1.NFI_TraceResult.div_prefix])
    else if mode == "proof3" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.word_product, `AspisR1.RPx_Deployed.deployed, `AspisR1.NFI_InnerTrace.frames, `AspisR1.NFI_WrapperDomains.reached])
    else if mode == "proof4" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedOuterStep.active, `AspisR1.NFF_FullWrapper.headline, `AspisR1.NFI_OpeningFrame.original_byte, `AspisR1.NFI_WrapperTrace.erased])
    else if mode == "proof5" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_RawLog.replay, `AspisR1.NFF_LoggedTail.replay, `AspisR1.NFI_OpeningFrame.same_heap_frame, `AspisR1.NFI_WrapperTrace.headline])
    else if mode == "proof6" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_BaseMultiply.source, `AspisR1.NFE_DotBridge.one, `AspisR1.NFI_OpeningFrame.arbitrary_complement])
    else if mode == "proof7" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedOuterStep.stopped, `AspisR1.NFF_LoggedEight.cell_replay, `AspisR1.NFI_OpeningFrame.receiver_and_return_frame])
    else if mode == "proof8" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_RawTypedLog.canonical, `AspisR1.NFF_LoggedWrapper.replay, `AspisR1.NFI_OuterActual.emitted])
    else if mode == "proof9" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_Cell.replay, `AspisR1.NFE_WrapperBridge.four, `AspisR1.NFI_OuterCut.same_input])
    else if mode == "proof10" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedPush.private_replay, `AspisR1.NFF_LoggedEight.replay, `AspisR1.NFI_OuterCut.erased])
    else if mode == "proof11" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_RawTypedLog.operands, `AspisR1.NFF_LoggedWrapper.headline, `AspisR1.NFI_OuterTrace.replay])
    else if mode == "proof12" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_Cell.primitive_reply, `AspisR1.NFF_LoggedDomains.one, `AspisR1.NFI_OuterTrace.frames])
    else if mode == "proof13" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedPush.public_replay, `AspisR1.NFF_LoggedLoop.replay, `AspisR1.NFI_PrivateCuts.installed])
    else if mode == "proof14" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_RawTypedLog.replay, `AspisR1.NFF_ProductCall.replay, `AspisR1.NFI_SingleDomains.reached])
    else if mode == "proof15" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_CoreReduction.same, `AspisR1.NFF_LoggedDomains.four, `AspisR1.NFI_SingleTrace.main_erased])
    else if mode == "proof16" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedRaw.replay, `AspisR1.NFF_LoggedOne.replay, `AspisR1.NFI_SingleTrace.erased])
    else if mode == "proof17" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_ReadDomains.canonical, `AspisR1.NFF_RawLog.natural, `AspisR1.NFI_SingleTrace.emitted])
    else if mode == "proof18" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_CoreReduction.source, `AspisR1.NFI_FailurePrefixes.rejected, `AspisR1.NFI_TailTrace.erased])
    else if mode == "proof19" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedRaw.headline, `AspisR1.NFI_FailurePrefixes.trace_prefix, `AspisR1.NFI_TailTrace.emitted])
    else if mode == "proof20" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_ReadDomains.selected, `AspisR1.NFI_InnerActual.emitted, `AspisR1.NFI_TraceResult.erase_bind])
    else if mode == "proof21" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_FullOne.replay, `AspisR1.NFI_InnerActual.borrowed_frame, `AspisR1.NFI_TraceResult.erase_lift])
    else if mode == "proof22" then
      (#[`NFI_CombinedFinal], #[`AspisR1.NFF_LoggedStep.update_replay, `AspisR1.NFI_InnerActual.canonical_at_cut, `AspisR1.NFI_TraceResult.erase_mark])
    else if mode == "scan" then (#[`NFI_CombinedFinal], #[])
    else if mode == "fixtures" then
      (#[`NEP_Planted, `NEP_Mutations],
       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,
         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,
         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])
    else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines "NFI_EXPECTED_IMPORTS.jsonl" do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env "NFI_LOADED_scan.jsonl" expected
    IO.println (if failed then "NFI_SCAN_FAILED" else "NFI_SCAN_ZERO_DANGLING")
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

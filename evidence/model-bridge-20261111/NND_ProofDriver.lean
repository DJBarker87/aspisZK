import Lean
import NFA_WALKER
import NFA_MemoryLimit
open Lean Elab Command
unsafe def main (args : List String) : IO UInt32 := do
 NFA_MemoryLimit.set
 initSearchPath (← findSysroot)
 enableInitializersExecution
 let mode := args.headD "invalid"
 let (modules, roots) ←
  if mode == "planted" then
   pure (#[`NEP_Planted],#[`NEP_Planted.matcher,`NEP_Planted.viaPrivate,`NEP_Planted.proof,`NEP_Planted.viaAux])
  else if mode == "mutations" then
   pure (#[`NEP_Mutations],#[`NEP_MutateMatch.matcher,`NEP_MutatePrivate.viaPrivate,`NEP_MutateProof.proof,`NEP_MutateAux.viaAux])
  else if mode == "closure" then pure (#[`NND_COMBINED_IMPORT],#[])
  else do
   let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NND_AUDIT_ROOTS.json"))
   let groups ← IO.ofExcept (manifest.getObjValAs? (Array (Array String)) "groups")
   let some idx := (mode.drop 5).toString.toNat? | throw (IO.userError "invalid proof mode")
   let some names := groups[idx]? | throw (IO.userError "proof group out of range")
   let selected ← IO.ofExcept (Json.parse (← IO.FS.readFile "NND_AUDIT_MODULES.json"))
   let selected ← IO.ofExcept (fromJson? selected : Except String (Array (Array String)))
   let some modules := selected[idx]? | throw (IO.userError "module group out of range")
   pure (modules.map String.toName,names.map String.toName)
 let env ← importModules (modules.map fun n => ({module:=n,importAll:=true}:Import))
  {} (loadExts:=true) (level:=.private)
 if mode == "closure" then
  IO.FS.writeFile "NND_CLOSURE_MODULES.json" (toJson (env.header.moduleNames.map Name.toString)).compress
  IO.println "NND_CLOSURE_LOADED"
  return 0
 IO.FS.createDirAll "NND_audit"
 let ctx : Command.Context := {fileName:="NND_ProofDriver",fileMap:=FileMap.ofString "",snap?:=none,cancelTk?:=none}
 let action : CommandElabM Bool := do
  let mut failed := false
  for root in roots do
   try
    elabCommand (← `(command| #print axioms $(mkIdent root)))
    NEP.audit root ("NND_audit/NND_" ++ mode ++ "_" ++ root.toString)
   catch e =>
    logInfo m!"NND_AUDIT_EXCEPTION {root}: {e.toMessageData}"
    failed := true
  return failed
 let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
 match result with
 | .error e =>
  IO.eprintln (← e.toMessageData.toString)
  return 2
 | .ok (failed,state) =>
  for msg in state.messages.toList do IO.println (← msg.data.toString)
  return if failed then 1 else 0

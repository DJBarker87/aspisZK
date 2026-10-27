import Lean
import LPn_DotClosed
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  for m in env.header.modules do
    logInfo m!"KSA_IMPORT {m.module}"
  for (n,c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module.toString
      if #["XR","XS","LP"].any owner.startsWith then
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        let thm := match c with | .thmInfo _ => true | _ => false
        logInfo m!"KSA_DEP {(Json.mkObj [("name",toJson n.toString),("module",toJson owner),("theorem",toJson thm),("refs",toJson (refs.map Name.toString))]).compress}"

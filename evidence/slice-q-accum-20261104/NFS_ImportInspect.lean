import NFS_NEV_AccumPacket
import Lean
run_cmd do
 let e ← Lean.getEnv
 for i in [:e.header.moduleNames.size] do
  Lean.logInfo ("NFS_MODULE " ++ (Lean.Json.mkObj [("module",Lean.toJson e.header.moduleNames[i]!.toString),("imports",Lean.toJson (e.header.moduleData[i]!.imports.map fun x=>x.module.toString))]).compress)

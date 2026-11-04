import Lean
import NGK_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @NGK_NFO_PacketDecoder.on_packet
#print axioms NGK_NFO_PacketDecoder.on_packet
#check @NGK_NFR_AfterstateForward08.result
#print axioms NGK_NFR_AfterstateForward08.result
#check @NGK_NFR_ResultForwardHelpers.digest_range
#print axioms NGK_NFR_ResultForwardHelpers.digest_range
#check @NGK_NFV_RequestWindows.envelope
#print axioms NGK_NFV_RequestWindows.envelope

run_cmd do
 let env ← Lean.getEnv
 let n := `NGK_NFO_PacketDecoder.on_packet
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFO_PacketDecoder do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_AfterstateForward08.result
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_AfterstateForward08 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_ResultForwardHelpers.digest_range
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_ResultForwardHelpers do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFV_RequestWindows.envelope
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFV_RequestWindows do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"

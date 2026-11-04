import Lean
import NGK_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @NGK_NFO_PoolReturnData.association
#print axioms NGK_NFO_PoolReturnData.association
#check @NGK_NFR_AfterstateForwardHelpers.twenty_eta
#print axioms NGK_NFR_AfterstateForwardHelpers.twenty_eta
#check @NGK_NFR_ResultForwardHelpers.get7
#print axioms NGK_NFR_ResultForwardHelpers.get7
#check @NGK_NFV_HelperModel.erase
#print axioms NGK_NFV_HelperModel.erase

run_cmd do
 let env ← Lean.getEnv
 let n := `NGK_NFO_PoolReturnData.association
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFO_PoolReturnData do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_AfterstateForwardHelpers.twenty_eta
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_AfterstateForwardHelpers do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_ResultForwardHelpers.get7
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_ResultForwardHelpers do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFV_HelperModel.erase
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFV_HelperModel do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"

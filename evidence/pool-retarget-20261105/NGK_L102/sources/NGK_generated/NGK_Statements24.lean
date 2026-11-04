import Lean
import NGK_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @NGK_NFO_DecodeReject.wrong_length
#print axioms NGK_NFO_DecodeReject.wrong_length
#check @NGK_NFR_ExtractedDecode.oracle
#print axioms NGK_NFR_ExtractedDecode.oracle
#check @NGK_NFV_Copy.suffix
#print axioms NGK_NFV_Copy.suffix

run_cmd do
 let env ← Lean.getEnv
 let n := `NGK_NFO_DecodeReject.wrong_length
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFO_DecodeReject do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_ExtractedDecode.oracle
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_ExtractedDecode do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFV_Copy.suffix
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFV_Copy do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"

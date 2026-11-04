import Lean
import NGK_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @NGK_NFO_FlatMapInjective.uniform
#print axioms NGK_NFO_FlatMapInjective.uniform
#check @NGK_NFR_AfterstateForward.roundtrip
#print axioms NGK_NFR_AfterstateForward.roundtrip
#check @NGK_NFR_ResultForward.emitted
#print axioms NGK_NFR_ResultForward.emitted
#check @NGK_NFV_RequestIndexes.header
#print axioms NGK_NFV_RequestIndexes.header

run_cmd do
 let env ← Lean.getEnv
 let n := `NGK_NFO_FlatMapInjective.uniform
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFO_FlatMapInjective do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_AfterstateForward.roundtrip
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_AfterstateForward do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFR_ResultForward.emitted
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFR_ResultForward do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"
 let n := `NGK_NFV_RequestIndexes.header
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGK_NFV_RequestIndexes do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGK_CERT_ENTRY {entry.compress}"

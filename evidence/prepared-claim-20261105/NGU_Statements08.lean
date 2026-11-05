import Lean
import NGU_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @AspisR1.NGU_LPr_WordValue.bits._proof_14
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_14
#check @AspisR1.NGU_LPr_WordValue.bits._proof_15
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_15
#check @AspisR1.NGU_LPr_WordValue.bits._proof_16
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_16
#check @AspisR1.NGU_LPr_WordValue.bits._proof_17
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_17
#check @AspisR1.NGU_LPr_WordValue.bits._proof_18
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_18
#check @AspisR1.NGU_LPr_WordValue.bits._proof_19
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_19
#check @AspisR1.NGU_LPr_WordValue.bits._proof_2
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_2
#check @AspisR1.NGU_LPr_WordValue.bits._proof_20
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_20
#check @AspisR1.NGU_LPr_WordValue.bits._proof_21
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_21
#check @AspisR1.NGU_LPr_WordValue.bits._proof_22
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_22
#check @AspisR1.NGU_LPr_WordValue.bits._proof_23
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_23
#check @AspisR1.NGU_LPr_WordValue.bits._proof_24
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_24
#check @AspisR1.NGU_LPr_WordValue.bits._proof_25
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_25
#check @AspisR1.NGU_LPr_WordValue.bits._proof_26
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_26
#check @AspisR1.NGU_LPr_WordValue.bits._proof_27
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_27
#check @AspisR1.NGU_LPr_WordValue.bits._proof_28
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_28
#check @AspisR1.NGU_LPr_WordValue.bits._proof_29
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_29
#check @AspisR1.NGU_LPr_WordValue.bits._proof_3
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_3
#check @AspisR1.NGU_LPr_WordValue.bits._proof_30
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_30
#check @AspisR1.NGU_LPr_WordValue.bits._proof_31
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_31
#check @AspisR1.NGU_LPr_WordValue.bits._proof_32
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_32
#check @AspisR1.NGU_LPr_WordValue.bits._proof_33
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_33
#check @AspisR1.NGU_LPr_WordValue.bits._proof_34
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_34
#check @AspisR1.NGU_LPr_WordValue.bits._proof_35
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_35
#check @AspisR1.NGU_LPr_WordValue.bits._proof_36
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_36
#check @AspisR1.NGU_LPr_WordValue.bits._proof_37
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_37
#check @AspisR1.NGU_LPr_WordValue.bits._proof_38
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_38
#check @AspisR1.NGU_LPr_WordValue.bits._proof_39
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_39
#check @AspisR1.NGU_LPr_WordValue.bits._proof_4
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_4
#check @AspisR1.NGU_LPr_WordValue.bits._proof_40
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_40
#check @AspisR1.NGU_LPr_WordValue.bits._proof_5
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_5
#check @AspisR1.NGU_LPr_WordValue.bits._proof_6
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_6
#check @AspisR1.NGU_LPr_WordValue.bits._proof_7
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_7

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_14
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_15
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_16
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_17
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_18
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_19
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_20
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_21
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_22
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_23
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_24
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_25
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_26
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_27
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_28
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_29
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_30
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_31
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_32
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_33
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_34
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_35
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_36
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_37
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_38
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_39
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_40
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_7
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

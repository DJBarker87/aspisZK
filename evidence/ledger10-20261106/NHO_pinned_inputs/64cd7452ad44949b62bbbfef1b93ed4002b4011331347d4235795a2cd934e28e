import Lean
import NGU_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @AspisR1.NGU_LPq_SixPoints.domain._proof_1
#print axioms AspisR1.NGU_LPq_SixPoints.domain._proof_1
#check @AspisR1.NGU_LPq_SixPoints.selected
#print axioms AspisR1.NGU_LPq_SixPoints.selected
#check @AspisR1.NGU_LPq_SixPoints.selected._proof_1
#print axioms AspisR1.NGU_LPq_SixPoints.selected._proof_1
#check @AspisR1.NGU_LPr_SelectedBytes.selected
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_1
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_1
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_2
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_2
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_3
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_3
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_4
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_4
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_5
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_5
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_6
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_6
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_7
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_7
#check @AspisR1.NGU_LPr_SelectedBytes.selected._proof_8
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._proof_8
#check @AspisR1.NGU_LPr_SelectedBytes.selected._simp_5
#print axioms AspisR1.NGU_LPr_SelectedBytes.selected._simp_5
#check @AspisR1.NGU_LPr_SelectedWords.byte._proof_1
#print axioms AspisR1.NGU_LPr_SelectedWords.byte._proof_1
#check @AspisR1.NGU_LPr_SelectedWords.byte.eq_1
#print axioms AspisR1.NGU_LPr_SelectedWords.byte.eq_1
#check @AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_1
#print axioms AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_1
#check @AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_2
#print axioms AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_2
#check @AspisR1.NGU_LPr_SelectedWords.naturalWord.eq_1
#print axioms AspisR1.NGU_LPr_SelectedWords.naturalWord.eq_1
#check @AspisR1.NGU_LPr_SelectedWords.selected_words
#print axioms AspisR1.NGU_LPr_SelectedWords.selected_words
#check @AspisR1.NGU_LPr_SelectedWords.window_byte
#print axioms AspisR1.NGU_LPr_SelectedWords.window_byte
#check @AspisR1.NGU_LPr_SelectedWords.window_word
#print axioms AspisR1.NGU_LPr_SelectedWords.window_word
#check @AspisR1.NGU_LPr_SelectedWords.window_word._proof_1
#print axioms AspisR1.NGU_LPr_SelectedWords.window_word._proof_1
#check @AspisR1.NGU_LPr_SelectedWords.window_word._proof_2
#print axioms AspisR1.NGU_LPr_SelectedWords.window_word._proof_2
#check @AspisR1.NGU_LPr_SelectedWords.window_word._proof_3
#print axioms AspisR1.NGU_LPr_SelectedWords.window_word._proof_3
#check @AspisR1.NGU_LPr_SelectedWords.window_word._proof_4
#print axioms AspisR1.NGU_LPr_SelectedWords.window_word._proof_4
#check @AspisR1.NGU_LPr_WordNat.append_value
#print axioms AspisR1.NGU_LPr_WordNat.append_value
#check @AspisR1.NGU_LPr_WordNat.value
#print axioms AspisR1.NGU_LPr_WordNat.value
#check @AspisR1.NGU_LPr_WordNat.value._proof_1
#print axioms AspisR1.NGU_LPr_WordNat.value._proof_1
#check @AspisR1.NGU_LPr_WordValue.bits
#print axioms AspisR1.NGU_LPr_WordValue.bits
#check @AspisR1.NGU_LPr_WordValue.bits._proof_1
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_1
#check @AspisR1.NGU_LPr_WordValue.bits._proof_10
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_10
#check @AspisR1.NGU_LPr_WordValue.bits._proof_11
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_11
#check @AspisR1.NGU_LPr_WordValue.bits._proof_12
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_12
#check @AspisR1.NGU_LPr_WordValue.bits._proof_13
#print axioms AspisR1.NGU_LPr_WordValue.bits._proof_13

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SixPoints.domain._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SixPoints.selected
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SixPoints.selected._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_7
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._proof_8
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedBytes.selected._simp_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.byte._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.byte.eq_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.nativeWord._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.naturalWord.eq_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.selected_words
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_byte
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_word
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_word._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_word._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_word._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_SelectedWords.window_word._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordNat.append_value
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordNat.value
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordNat.value._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_10
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_11
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_12
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPr_WordValue.bits._proof_13
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

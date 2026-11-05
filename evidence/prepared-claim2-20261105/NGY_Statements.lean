import Lean
import NGY_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true

#check @AspisR1.NGY_Association.step
#print axioms AspisR1.NGY_Association.step
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Association.step
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Association do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Complete.step
#print axioms AspisR1.NGY_Complete.step
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Complete.step
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Complete do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Coverage.point_cases
#print axioms AspisR1.NGY_Coverage.point_cases
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Coverage.point_cases
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Coverage do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Coverage.six
#print axioms AspisR1.NGY_Coverage.six
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Coverage.six
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Coverage do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Coverage.lane_cases
#print axioms AspisR1.NGY_Coverage.lane_cases
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Coverage.lane_cases
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Coverage do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Coverage.tiles
#print axioms AspisR1.NGY_Coverage.tiles
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Coverage.tiles
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Coverage do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Decoder.limbs
#print axioms AspisR1.NGY_Decoder.limbs
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Decoder.limbs
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Decoder do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Decoder.bytes
#print axioms AspisR1.NGY_Decoder.bytes
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Decoder.bytes
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Decoder do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Decoder.selected
#print axioms AspisR1.NGY_Decoder.selected
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Decoder.selected
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Decoder do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_DirectRead.source
#print axioms AspisR1.NGY_DirectRead.source
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_DirectRead.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_DirectRead do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldOracle.association
#print axioms AspisR1.NGY_FieldOracle.association
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldOracle.association
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldOracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldOracle.error
#print axioms AspisR1.NGY_FieldOracle.error
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldOracle.error
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldOracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldOracle.source_step
#print axioms AspisR1.NGY_FieldOracle.source_step
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldOracle.source_step
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldOracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldSpec.limbs
#print axioms AspisR1.NGY_FieldSpec.limbs
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldSpec.limbs
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldSpec do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldSpec.bytes
#print axioms AspisR1.NGY_FieldSpec.bytes
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldSpec.bytes
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldSpec do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldSpec.source_local
#print axioms AspisR1.NGY_FieldSpec.source_local
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldSpec.source_local
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldSpec do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_FieldSpec.source
#print axioms AspisR1.NGY_FieldSpec.source
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_FieldSpec.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_FieldSpec do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Loop.from_invariant
#print axioms AspisR1.NGY_Loop.from_invariant
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Loop.from_invariant
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Loop do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Loop.installed_step
#print axioms AspisR1.NGY_Loop.installed_step
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Loop.installed_step
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Loop do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Oracle.reference_eq_G
#print axioms AspisR1.NGY_Oracle.reference_eq_G
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Oracle.reference_eq_G
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Oracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Oracle.child
#print axioms AspisR1.NGY_Oracle.child
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Oracle.child
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Oracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Oracle.frame
#print axioms AspisR1.NGY_Oracle.frame
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Oracle.frame
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Oracle do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Result.association
#print axioms AspisR1.NGY_Result.association
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Result.association
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Result do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Result.error
#print axioms AspisR1.NGY_Result.error
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Result.error
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Result do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Result.success
#print axioms AspisR1.NGY_Result.success
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Result.success
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Result do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_SourceStep.source
#print axioms AspisR1.NGY_SourceStep.source
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_SourceStep.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_SourceStep do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Thread.logged_post
#print axioms AspisR1.NGY_Thread.logged_post
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Thread.logged_post
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Thread do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Thread.records
#print axioms AspisR1.NGY_Thread.records
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Thread.records
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Thread do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Thread.from_invariant
#print axioms AspisR1.NGY_Thread.from_invariant
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Thread.from_invariant
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Thread do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Unified.semantic
#print axioms AspisR1.NGY_Unified.semantic
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Unified.semantic
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Unified do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Unified.decoded
#print axioms AspisR1.NGY_Unified.decoded
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Unified.decoded
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Unified do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Unified.operand_log
#print axioms AspisR1.NGY_Unified.operand_log
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Unified.operand_log
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Unified do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Window.selected
#print axioms AspisR1.NGY_Window.selected
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Window.selected
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Window do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Window.bounded
#print axioms AspisR1.NGY_Window.bounded
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Window.bounded
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Window do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Window.frame
#print axioms AspisR1.NGY_Window.frame
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Window.frame
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Window do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

#check @AspisR1.NGY_Window.disjoint
#print axioms AspisR1.NGY_Window.disjoint
run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGY_Window.disjoint
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGY_Window do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGY_CERT_ENTRY {entry.compress}"

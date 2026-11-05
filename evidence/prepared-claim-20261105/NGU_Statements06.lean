import Lean
import NGU_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @AspisR1.NGU_LPq_OutputDomains.point
#print axioms AspisR1.NGU_LPq_OutputDomains.point
#check @AspisR1.NGU_LPq_OutputDomains.powers
#print axioms AspisR1.NGU_LPq_OutputDomains.powers
#check @AspisR1.NGU_LPq_PointConstruct.ReadDomain._proof_1
#print axioms AspisR1.NGU_LPq_PointConstruct.ReadDomain._proof_1
#check @AspisR1.NGU_LPq_PointConstruct.from_zero
#print axioms AspisR1.NGU_LPq_PointConstruct.from_zero
#check @AspisR1.NGU_LPq_PointConstruct.loop
#print axioms AspisR1.NGU_LPq_PointConstruct.loop
#check @AspisR1.NGU_LPq_PointConstruct.loop._proof_1
#print axioms AspisR1.NGU_LPq_PointConstruct.loop._proof_1
#check @AspisR1.NGU_LPq_PointConstruct.loop._proof_2
#print axioms AspisR1.NGU_LPq_PointConstruct.loop._proof_2
#check @AspisR1.NGU_LPq_PointConstruct.loop._proof_3
#print axioms AspisR1.NGU_LPq_PointConstruct.loop._proof_3
#check @AspisR1.NGU_LPq_PointConstruct.loop._proof_4
#print axioms AspisR1.NGU_LPq_PointConstruct.loop._proof_4
#check @AspisR1.NGU_LPq_PreparedClaim.native_result
#print axioms AspisR1.NGU_LPq_PreparedClaim.native_result
#check @AspisR1.NGU_LPq_PreparedClaim.program._proof_1
#print axioms AspisR1.NGU_LPq_PreparedClaim.program._proof_1
#check @AspisR1.NGU_LPq_PreparedClaim.program_eq
#print axioms AspisR1.NGU_LPq_PreparedClaim.program_eq
#check @AspisR1.NGU_LPq_PreparedClaim.uniqueness
#print axioms AspisR1.NGU_LPq_PreparedClaim.uniqueness
#check @AspisR1.NGU_LPq_PreparedTrace.construct
#print axioms AspisR1.NGU_LPq_PreparedTrace.construct
#check @AspisR1.NGU_LPq_PreparedTrace.initial._proof_1
#print axioms AspisR1.NGU_LPq_PreparedTrace.initial._proof_1
#check @AspisR1.NGU_LPq_PreparedTrace.initial._proof_2
#print axioms AspisR1.NGU_LPq_PreparedTrace.initial._proof_2
#check @AspisR1.NGU_LPq_PreparedTrace.initial_canonical
#print axioms AspisR1.NGU_LPq_PreparedTrace.initial_canonical
#check @AspisR1.NGU_LPq_PreparedTrace.source
#print axioms AspisR1.NGU_LPq_PreparedTrace.source
#check @AspisR1.NGU_LPq_PreparedTrace.zero_claim
#print axioms AspisR1.NGU_LPq_PreparedTrace.zero_claim
#check @AspisR1.NGU_LPq_ReadPorts.SemCanonical._proof_1
#print axioms AspisR1.NGU_LPq_ReadPorts.SemCanonical._proof_1
#check @AspisR1.NGU_LPq_ReadPorts.backQ.eq_1
#print axioms AspisR1.NGU_LPq_ReadPorts.backQ.eq_1
#check @AspisR1.NGU_LPq_ReadPorts.e_roundtrip
#print axioms AspisR1.NGU_LPq_ReadPorts.e_roundtrip
#check @AspisR1.NGU_LPq_ReadPorts.five_domains
#print axioms AspisR1.NGU_LPq_ReadPorts.five_domains
#check @AspisR1.NGU_LPq_ReadPorts.q_roundtrip
#print axioms AspisR1.NGU_LPq_ReadPorts.q_roundtrip
#check @AspisR1.NGU_LPq_ReadPorts.semantic
#print axioms AspisR1.NGU_LPq_ReadPorts.semantic
#check @AspisR1.NGU_LPq_ReadPorts.semantic._proof_1
#print axioms AspisR1.NGU_LPq_ReadPorts.semantic._proof_1
#check @AspisR1.NGU_LPq_ReadPorts.weights
#print axioms AspisR1.NGU_LPq_ReadPorts.weights
#check @AspisR1.NGU_LPq_SelectedDomain.native_result
#print axioms AspisR1.NGU_LPq_SelectedDomain.native_result
#check @AspisR1.NGU_LPq_SelectedDomain.selected._proof_1
#print axioms AspisR1.NGU_LPq_SelectedDomain.selected._proof_1
#check @AspisR1.NGU_LPq_SelectedDomain.selected._proof_2
#print axioms AspisR1.NGU_LPq_SelectedDomain.selected._proof_2
#check @AspisR1.NGU_LPq_SelectedDomain.selected_fields
#print axioms AspisR1.NGU_LPq_SelectedDomain.selected_fields
#check @AspisR1.NGU_LPq_SixPoints.construct
#print axioms AspisR1.NGU_LPq_SixPoints.construct
#check @AspisR1.NGU_LPq_SixPoints.domain
#print axioms AspisR1.NGU_LPq_SixPoints.domain

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OutputDomains.point
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OutputDomains.powers
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.ReadDomain._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.from_zero
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.loop
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.loop._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.loop._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.loop._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PointConstruct.loop._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedClaim.native_result
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedClaim.program._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedClaim.program_eq
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedClaim.uniqueness
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.construct
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.initial._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.initial._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.initial_canonical
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_PreparedTrace.zero_claim
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.SemCanonical._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.backQ.eq_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.e_roundtrip
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.five_domains
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.q_roundtrip
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.semantic
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.semantic._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ReadPorts.weights
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SelectedDomain.native_result
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SelectedDomain.selected._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SelectedDomain.selected._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SelectedDomain.selected_fields
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SixPoints.construct
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_SixPoints.domain
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

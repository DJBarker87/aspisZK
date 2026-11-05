import Lean
import NGU_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_1
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_1
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_2
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_2
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_3
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_3
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_4
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_4
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_5
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_5
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_6
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_6
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_7
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_7
#check @AspisR1.NGU_LPq_ExpandedWords.high._proof_8
#print axioms AspisR1.NGU_LPq_ExpandedWords.high._proof_8
#check @AspisR1.NGU_LPq_ExpandedWords.low
#print axioms AspisR1.NGU_LPq_ExpandedWords.low
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_1
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_1
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_2
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_2
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_3
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_3
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_4
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_4
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_5
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_5
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_6
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_6
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_7
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_7
#check @AspisR1.NGU_LPq_ExpandedWords.low._proof_8
#print axioms AspisR1.NGU_LPq_ExpandedWords.low._proof_8
#check @AspisR1.NGU_LPq_ExpandedWords.word.eq_1
#print axioms AspisR1.NGU_LPq_ExpandedWords.word.eq_1
#check @AspisR1.NGU_LPq_IndexPorts.add
#print axioms AspisR1.NGU_LPq_IndexPorts.add
#check @AspisR1.NGU_LPq_IndexPorts.add._proof_1
#print axioms AspisR1.NGU_LPq_IndexPorts.add._proof_1
#check @AspisR1.NGU_LPq_IndexPorts.mul
#print axioms AspisR1.NGU_LPq_IndexPorts.mul
#check @AspisR1.NGU_LPq_IndexPorts.mul._proof_1
#print axioms AspisR1.NGU_LPq_IndexPorts.mul._proof_1
#check @AspisR1.NGU_LPq_OuterConstruct.loop
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_1
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_1
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_2
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_2
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_3
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_3
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_4
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_4
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_5
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_5
#check @AspisR1.NGU_LPq_OuterConstruct.loop._proof_6
#print axioms AspisR1.NGU_LPq_OuterConstruct.loop._proof_6
#check @AspisR1.NGU_LPq_OuterTrace.Trace.brecOn
#print axioms AspisR1.NGU_LPq_OuterTrace.Trace.brecOn
#check @AspisR1.NGU_LPq_OuterTrace.point_source
#print axioms AspisR1.NGU_LPq_OuterTrace.point_source
#check @AspisR1.NGU_LPq_OuterTrace.source
#print axioms AspisR1.NGU_LPq_OuterTrace.source
#check @AspisR1.NGU_LPq_OutputDomains.finish
#print axioms AspisR1.NGU_LPq_OutputDomains.finish

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_7
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.high._proof_8
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_7
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.low._proof_8
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_ExpandedWords.word.eq_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_IndexPorts.add
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_IndexPorts.add._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_IndexPorts.mul
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_IndexPorts.mul._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part004 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterConstruct.loop._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterTrace.Trace.brecOn
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterTrace.point_source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OuterTrace.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part006 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_LPq_OutputDomains.finish
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part005 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

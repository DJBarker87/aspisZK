import Lean
import NGU_COMBINED_IMPORT
open Lean
set_option pp.universes true
set_option pp.explicit true
#check @AspisR1.NGU_ClaimOps.add
#print axioms AspisR1.NGU_ClaimOps.add
#check @AspisR1.NGU_ClaimOps.claim_back
#print axioms AspisR1.NGU_ClaimOps.claim_back
#check @AspisR1.NGU_ClaimOps.multiply
#print axioms AspisR1.NGU_ClaimOps.multiply
#check @AspisR1.NGU_JGi_FinishFields.source
#print axioms AspisR1.NGU_JGi_FinishFields.source
#check @AspisR1.NGU_LPf_ArrayFour.list_shape
#print axioms AspisR1.NGU_LPf_ArrayFour.list_shape
#check @AspisR1.NGU_LPf_ArrayFour.list_shape._proof_1
#print axioms AspisR1.NGU_LPf_ArrayFour.list_shape._proof_1
#check @AspisR1.NGU_LPf_ArrayFour.shape
#print axioms AspisR1.NGU_LPf_ArrayFour.shape
#check @AspisR1.NGU_LPf_DotFinish.source
#print axioms AspisR1.NGU_LPf_DotFinish.source
#check @AspisR1.NGU_LPf_DotPushCut.source
#print axioms AspisR1.NGU_LPf_DotPushCut.source
#check @AspisR1.NGU_LPf_DotPushFour.source
#print axioms AspisR1.NGU_LPf_DotPushFour.source
#check @AspisR1.NGU_LPf_DotPushFour.source._proof_1
#print axioms AspisR1.NGU_LPf_DotPushFour.source._proof_1
#check @AspisR1.NGU_LPf_DotPushStep.source
#print axioms AspisR1.NGU_LPf_DotPushStep.source
#check @AspisR1.NGU_LPf_DotResidueStep.source
#print axioms AspisR1.NGU_LPf_DotResidueStep.source
#check @AspisR1.NGU_LPf_DotWordStep.fold_bound
#print axioms AspisR1.NGU_LPf_DotWordStep.fold_bound
#check @AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_1
#print axioms AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_1
#check @AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_2
#print axioms AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_2
#check @AspisR1.NGU_LPf_DotWordStep.reduced
#print axioms AspisR1.NGU_LPf_DotWordStep.reduced
#check @AspisR1.NGU_LPf_DotWordStep.value
#print axioms AspisR1.NGU_LPf_DotWordStep.value
#check @AspisR1.NGU_LPf_DotWordStep.value._proof_1
#print axioms AspisR1.NGU_LPf_DotWordStep.value._proof_1
#check @AspisR1.NGU_LPf_PublicDotAllStates.source
#print axioms AspisR1.NGU_LPf_PublicDotAllStates.source
#check @AspisR1.NGU_LPf_PublicDotFinish.source
#print axioms AspisR1.NGU_LPf_PublicDotFinish.source
#check @AspisR1.NGU_LPi_CheckedInputs.canonical
#print axioms AspisR1.NGU_LPi_CheckedInputs.canonical
#check @AspisR1.NGU_LPi_CheckedInputs.canonical._proof_3
#print axioms AspisR1.NGU_LPi_CheckedInputs.canonical._proof_3
#check @AspisR1.NGU_LPi_CheckedInputs.canonical._proof_4
#print axioms AspisR1.NGU_LPi_CheckedInputs.canonical._proof_4
#check @AspisR1.NGU_LPi_CheckedInputs.canonical._proof_5
#print axioms AspisR1.NGU_LPi_CheckedInputs.canonical._proof_5
#check @AspisR1.NGU_LPi_CheckedInputs.canonical._proof_6
#print axioms AspisR1.NGU_LPi_CheckedInputs.canonical._proof_6
#check @AspisR1.NGU_LPi_CheckedInputs.checked
#print axioms AspisR1.NGU_LPi_CheckedInputs.checked
#check @AspisR1.NGU_LPi_CheckedInputs.checked._proof_1
#print axioms AspisR1.NGU_LPi_CheckedInputs.checked._proof_1
#check @AspisR1.NGU_LPi_CheckedInputs.checked._proof_2
#print axioms AspisR1.NGU_LPi_CheckedInputs.checked._proof_2
#check @AspisR1.NGU_LPi_CheckedInputs.checked._proof_3
#print axioms AspisR1.NGU_LPi_CheckedInputs.checked._proof_3
#check @AspisR1.NGU_LPi_CheckedInputs.checked._proof_4
#print axioms AspisR1.NGU_LPi_CheckedInputs.checked._proof_4
#check @AspisR1.NGU_LPi_CheckedInputs.from_wide
#print axioms AspisR1.NGU_LPi_CheckedInputs.from_wide
#check @AspisR1.NGU_LPi_CheckedInputs.q._proof_1
#print axioms AspisR1.NGU_LPi_CheckedInputs.q._proof_1

run_cmd do
 let env ← Lean.getEnv
 let n := `AspisR1.NGU_ClaimOps.add
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_ClaimOps do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_ClaimOps.claim_back
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_ClaimOps do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_ClaimOps.multiply
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_ClaimOps do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_JGi_FinishFields.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part007 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_ArrayFour.list_shape
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_ArrayFour.list_shape._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_ArrayFour.shape
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotFinish.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotPushCut.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotPushFour.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotPushFour.source._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotPushStep.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotResidueStep.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part003 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.fold_bound
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.fold_bound._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.reduced
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.value
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_DotWordStep.value._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_PublicDotAllStates.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPf_PublicDotFinish.source
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.canonical
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.canonical._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.canonical._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.canonical._proof_5
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.canonical._proof_6
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.checked
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.checked._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.checked._proof_2
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.checked._proof_3
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.checked._proof_4
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.from_wide
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"
 let n := `AspisR1.NGU_LPi_CheckedInputs.q._proof_1
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `NGU_Part000 do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {entry.compress}"

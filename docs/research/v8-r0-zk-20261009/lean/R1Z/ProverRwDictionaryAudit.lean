import R1Z.ProverRwDictionaryBaseField
import R1Z.ProverRwDictionaryCorrectQAdd
import R1Z.ProverRwDictionaryCorrectQMul
import R1Z.ProverRwDictionaryCorrectQSub
import R1Z.ProverRwDictionaryCorrectScalar
import R1Z.ProverRwDictionaryCorrectWAdd
import R1Z.ProverRwDictionaryCorrectWMul
import R1Z.ProverRwDictionaryCorrectWSub
import R1Z.ProverRwDictionaryDerived
import R1Z.ProverRwDictionaryDerivedSource
import R1Z.ProverRwDictionaryDigest
import R1Z.ProverRwDictionaryDomain
import R1Z.ProverRwDictionaryLayout
import R1Z.ProverRwDictionaryLayoutArithmetic
import R1Z.ProverRwDictionaryLayoutSource
import R1Z.ProverRwDictionaryLayoutTotal
import R1Z.ProverRwDictionaryLayoutValues
import R1Z.ProverRwDictionaryMerkle
import R1Z.ProverRwDictionarySamplers
import R1Z.ProverRwDictionaryScalar
import R1Z.ProverRwDictionaryTower
import R1Z.ProverRwDictionaryWideQM
import R1Z.ProverCommitDeployedFuel22

-- One focused audit of the final new declaration closure; not a release replay.
#print axioms R1Z.ProverRwDictionaryBaseField.entry57
#print axioms R1Z.ProverRwDictionaryBaseField.entry58
#print axioms R1Z.ProverRwDictionaryBaseField.entry73
#print axioms R1Z.ProverRwDictionaryBaseField.entry74
#print axioms R1Z.ProverRwDictionaryCorrectQAdd.correct
#print axioms R1Z.ProverRwDictionaryCorrectQMul.correct
#print axioms R1Z.ProverRwDictionaryCorrectQSub.correct
#print axioms R1Z.ProverRwDictionaryCorrectScalar.total
#print axioms R1Z.ProverRwDictionaryCorrectWAdd.correct
#print axioms R1Z.ProverRwDictionaryCorrectWMul.correct
#print axioms R1Z.ProverRwDictionaryCorrectWSub.source_sub
#print axioms R1Z.ProverRwDictionaryCorrectWSub.correct
#print axioms R1Z.ProverRwDictionaryDerived.c_status
#print axioms R1Z.ProverRwDictionaryDerived.q_status
#print axioms R1Z.ProverRwDictionaryDerived.m_clone
#print axioms R1Z.ProverRwDictionaryDerived.m_eq
#print axioms R1Z.ProverRwDictionaryDerived.q_clone
#print axioms R1Z.ProverRwDictionaryDerived.q_eq
#print axioms R1Z.ProverRwDictionaryDigest.clone_installed
#print axioms R1Z.ProverRwDictionaryDigest.digest_installed
#print axioms R1Z.ProverRwDictionaryDomain.new_source
#print axioms R1Z.ProverRwDictionaryDomain.get_source
#print axioms R1Z.ProverRwDictionaryDomain.accepted
#print axioms R1Z.ProverRwDictionaryDomain.rejected
#print axioms R1Z.ProverRwDictionaryLayout.entry237
#print axioms R1Z.ProverRwDictionaryLayout.entry241
#print axioms R1Z.ProverRwDictionaryLayout.entry242
#print axioms R1Z.ProverRwDictionaryLayout.entry243
#print axioms R1Z.ProverRwDictionaryLayout.entry244
#print axioms R1Z.ProverRwDictionaryLayout.entry245
#print axioms R1Z.ProverRwDictionaryLayoutArithmetic.add_eq
#print axioms R1Z.ProverRwDictionaryLayoutArithmetic.mul_eq
#print axioms R1Z.ProverRwDictionaryLayoutArithmetic.sub_eq
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_SEMANTIC_COMPACT_VALUES_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_verifier_SEMANTIC_BYTES_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_LOGICAL_SEMANTIC_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_COMPACT_SEMANTIC_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_Y1_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_COMPACT_Y1_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_INACTIVE_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_ROUND0_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_FOLDED_ROOT_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_ROUND1_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_FINAL_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_OPENINGS_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OPENING_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_OFF_NODES_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_MAX_NODES_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_FIXED_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_MAX_PROOF_total
#print axioms R1Z.ProverRwDictionaryLayoutTotal.r22_compact_PROOF_BYTES_total
#print axioms R1Z.ProverRwDictionaryLayoutValues.logical_semantic
#print axioms R1Z.ProverRwDictionaryLayoutValues.proof_bytes
#print axioms R1Z.ProverRwDictionaryLayoutValues.node_offset
#print axioms R1Z.ProverRwDictionaryLayoutValues.opening_offset
#print axioms R1Z.ProverRwDictionaryMerkle.private_leaf
#print axioms R1Z.ProverRwDictionarySamplers.roundtrip
#print axioms R1Z.ProverRwDictionarySamplers.gamma_installed
#print axioms R1Z.ProverRwDictionarySamplers.ordinary_installed
#print axioms R1Z.ProverRwDictionarySamplers.ordinary_rank
#print axioms R1Z.ProverRwDictionarySamplers.gamma_rank
#print axioms R1Z.ProverRwDictionaryScalar.entry42
#print axioms R1Z.ProverRwDictionaryScalar.entry52
#print axioms R1Z.ProverRwDictionaryScalar.entry55
#print axioms R1Z.ProverRwDictionaryScalar.entry56
#print axioms R1Z.ProverRwDictionaryScalar.entry57
#print axioms R1Z.ProverRwDictionaryScalar.entry58
#print axioms R1Z.ProverRwDictionaryScalar.entry59
#print axioms R1Z.ProverRwDictionaryScalar.entry61
#print axioms R1Z.ProverRwDictionaryScalar.entry65
#print axioms R1Z.ProverRwDictionaryScalar.entry66
#print axioms R1Z.ProverRwDictionaryScalar.entry70
#print axioms R1Z.ProverRwDictionaryScalar.entry73
#print axioms R1Z.ProverRwDictionaryScalar.entry74
#print axioms R1Z.ProverRwDictionaryScalar.entry87
#print axioms R1Z.ProverRwDictionaryScalar.entry88
#print axioms R1Z.ProverRwDictionaryScalar.entry89
#print axioms R1Z.ProverRwDictionaryScalar.entry90
#print axioms R1Z.ProverRwDictionaryScalar.entry91
#print axioms R1Z.ProverRwDictionaryScalar.entry92
#print axioms R1Z.ProverRwDictionaryScalar.entry93
#print axioms R1Z.ProverRwDictionaryScalar.entry94
#print axioms R1Z.ProverRwDictionaryScalar.entry95
#print axioms R1Z.ProverRwDictionaryScalar.entry96
#print axioms R1Z.ProverRwDictionaryScalar.entry97
#print axioms R1Z.ProverRwDictionaryScalar.entry98
#print axioms R1Z.ProverRwDictionaryScalar.entry99
#print axioms R1Z.ProverRwDictionaryScalar.entry102
#print axioms R1Z.ProverRwDictionaryScalar.entry103
#print axioms R1Z.ProverRwDictionaryScalar.entry104
#print axioms R1Z.ProverRwDictionaryScalar.entry106
#print axioms R1Z.ProverRwDictionaryScalar.entry108
#print axioms R1Z.ProverRwDictionaryTower.c_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.q_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.w_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.native_c_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.native_q_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.native_w_roundtrip
#print axioms R1Z.ProverRwDictionaryTower.mapResult_bind
#print axioms R1Z.ProverRwDictionaryTower.zero_installed
#print axioms R1Z.ProverRwDictionaryTower.q_add_installed
#print axioms R1Z.ProverRwDictionaryTower.q_sub_installed
#print axioms R1Z.ProverRwDictionaryTower.q_mul_installed
#print axioms R1Z.ProverRwDictionaryTower.w_embed_installed
#print axioms R1Z.ProverRwDictionaryTower.w_add_installed
#print axioms R1Z.ProverRwDictionaryTower.w_mul_installed
#print axioms R1Z.ProverRwDictionaryWideQM.installed
#print axioms R1Z.ProverRwDictionaryWideQM.correct

#print axioms R1Z.ProverRwDictionaryDomain.selected
#print axioms R1Z.ProverCommitDeployedFuel22.RustProverRefinement
#print R1Z.ProverCommitDeployedFuel22.RustProverRefinement

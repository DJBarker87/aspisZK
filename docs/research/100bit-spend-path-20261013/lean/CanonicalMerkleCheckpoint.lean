import R1CanonicalByteAddress
import R1CanonicalByteHash
import R1CanonicalOracleLog
import R1CanonicalMerkleProgram
import R1CanonicalMerkleRecovery
import R1MerkleC1Target
import R1CanonicalC1Recovery

/-! Focused canonical-byte-log and C1 recovery checkpoint. -/

#print axioms AspisR1.CanonicalByteAddress.length_le
#print axioms AspisR1.CanonicalByteAddress.toBytes_normalize
#print axioms AspisR1.CanonicalByteAddress.normalize_ofBytes
#print axioms AspisR1.CanonicalByteAddress.normalize_idem
#print axioms AspisR1.CanonicalByteAddress.canonical_ofBytes
#print axioms AspisR1.CanonicalByteHash.encode_of_length
#print axioms AspisR1.CanonicalByteHash.encode_toBytes
#print axioms AspisR1.CanonicalByteHash.toBytes_encode
#print axioms AspisR1.CanonicalByteHash.encode_canonical
#print axioms AspisR1.CanonicalByteHash.hashBytes_of_length
#print axioms AspisR1.CanonicalByteHash.hashBytes_toBytes_canonical
#print axioms AspisR1.CanonicalOracleLog.canonicalDecidable
#print axioms AspisR1.CanonicalOracleLog.mem_canonicalTrace
#print axioms AspisR1.CanonicalOracleLog.read_original
#print axioms AspisR1.CanonicalOracleLog.consistent
#print axioms AspisR1.CanonicalOracleLog.encoded_present
#print axioms AspisR1.CanonicalOracleLog.absent_encoded_not_read
#print axioms AspisR1.CanonicalOracleLog.target_cases
#print axioms AspisR1.CanonicalOracleLog.recover_or_bad
#print axioms AspisR1.CanonicalMerkleProgram.eval_program
#print axioms AspisR1.CanonicalMerkleProgram.read_of_input
#print axioms AspisR1.CanonicalMerkleProgram.fullTrace_bounded
#print axioms AspisR1.CanonicalMerkleProgram.reads_canonical
#print axioms AspisR1.CanonicalMerkleRecovery.recover_or_events
#print axioms AspisR1.MerkleC1Target.pred_init
#print axioms AspisR1.MerkleC1Target.mass
#print axioms AspisR1.CanonicalC1Recovery.recover_or_events

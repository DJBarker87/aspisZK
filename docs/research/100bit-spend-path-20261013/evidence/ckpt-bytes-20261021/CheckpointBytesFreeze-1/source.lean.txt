import CheckpointBytesScalar
import CheckpointBytesBoundaries
import CheckpointBytesAllocationBoundary
import CheckpointBytesETotal
import CheckpointBytesSparseE
import CheckpointBytesSparseK
import CheckpointBytesSparseDigest
import CheckpointBytesHeader
import CheckpointBytesQuery
import CheckpointBytesLookup
import OraclePortCkptAbi5Stage
import OraclePortCkptAbi5Decision

/-! Focused compatible-cache union, not production reader adoption. -/
#print axioms AspisR1.CheckpointBytesETotal.e_byte_all
#print axioms AspisR1.CheckpointBytesEC5.e_byte_c5
#print axioms AspisR1.CheckpointBytesBlocks.encode_c5
#print axioms AspisR1.CheckpointBytesSparseE.gamma_c5
#print axioms AspisR1.CheckpointBytesSparseE.kappa_c5
#print axioms AspisR1.CheckpointBytesSparseE.alpha0_c5
#print axioms AspisR1.CheckpointBytesSparseE.alpha1_c5
#print axioms AspisR1.CheckpointBytesSparseE.claim_c5
#print axioms AspisR1.CheckpointBytesSparseE.rhs_c5
#print axioms AspisR1.CheckpointBytesSparseK.rho_c5
#print axioms AspisR1.CheckpointBytesSparseK.power_c5
#print axioms AspisR1.CheckpointBytesSparseK.semantic_c5
#print axioms AspisR1.CheckpointBytesSparseK.coordinate0_c5
#print axioms AspisR1.CheckpointBytesSparseK.coordinate1_c5
#print axioms AspisR1.CheckpointBytesSparseK.coordinate2_c5
#print axioms AspisR1.CheckpointBytesSparseK.coordinate3_c5
#print axioms AspisR1.CheckpointBytesSparseK.weight_c5
#print axioms AspisR1.CheckpointBytesSparseDigest.proofHash_bytes
#print axioms AspisR1.CheckpointBytesSparseDigest.publicHash_bytes
#print axioms AspisR1.CheckpointBytesSparseDigest.state_bytes
#print axioms AspisR1.CheckpointBytesSparseDigest.root0_bytes
#print axioms AspisR1.CheckpointBytesSparseDigest.root1_bytes
#print axioms AspisR1.CheckpointBytesHeader.header_bytes
#print axioms AspisR1.CheckpointBytesQuery.query_bytes
#print axioms AspisR1.CheckpointBytesLookup.body_byte
#print axioms AspisR1.CheckpointBytesLookup.vector_byte
#print axioms AspisR1.CheckpointBytesBoundaries.k_accepts_trailing_byte
#print axioms AspisR1.CheckpointBytesAllocationBoundary.no_unconditional_success
#print axioms AspisR1.OraclePortCkptAbi5Stage.reached_stage
#print axioms AspisR1.OraclePortCkptAbi5Decision.decision_observation

import R1Z.ProverRwFullFuns
import R1Z.ProverRwFullSemantic
import R1Z.ProverRwWireTransport
import R1Z.ProverRwEmissionAdapters

/-! Audit the complete parameterized caller, including bodies not yet refined.
Passing this audit is neither a native dictionary instance nor a RunJoin. -/
#print axioms ProverRwFull.ExternalTypes
#print axioms ProverRwFull.ExternalFuns
#print axioms ProverRwFull.host_wire.SemanticTranscript.semantic
#print axioms ProverRwFull.prover.prove_masked_with_attempt
#print axioms ProverRwFull.prover.prove_masked_attempt
#print axioms ProverRwFull.prover.retry_attempt
#print axioms ProverRwFull.prover.prove_masked_retrying_with
#print axioms ProverRwFull.RealR1_client.prove_for_proof_accounts
#print axioms R1Z.ProverRwFullSampler.total

#print axioms R1Z.ProverRwFullSemantic.invalid_row
#print axioms R1Z.ProverRwFullSemantic.from_read
#print axioms R1Z.ProverRwWireTransport.sample

import R1Z.ProverCommitTLS23
import R1Z.ProverCommitTreeOps23
import R1Z.ProverCommitAdaptiveFuel23
import R1Z.ProverCommitAdaptiveLaw23
import R1Z.ProverCommitAdaptiveHistory23
import R1Z.ProverCommitPolicy23
import R1Z.ProverCommitDeployedFuel22

/-! Final focused changed-cone audit. No assertion of concrete Rust refinement. -/
#print axioms R1Z.ProverCommitTLS23.access_simulates
#print axioms R1Z.ProverCommitTLS23.access_frame
#print axioms R1Z.ProverCommitTLS23.schedule_simulates
#print axioms R1Z.ProverCommitTLS23.read_after_store
#print axioms R1Z.ProverCommitTreeOps23.writes_decode
#print axioms R1Z.ProverCommitTreeOps23.get_decode
#print axioms R1Z.ProverCommitTreeOps23.iterSteps_spec
#print axioms R1Z.ProverCommitTreeOps23.tree_iteration
#print axioms R1Z.ProverCommitAdaptiveFuel23.adaptive_exhaustion
#print axioms R1Z.ProverCommitAdaptiveFuel23.source_exhaustion
#print axioms R1Z.ProverCommitAdaptiveFuel23.adaptive_union
#print axioms R1Z.ProverCommitAdaptiveLaw23.lazy_exact
#print axioms R1Z.ProverCommitAdaptiveLaw23.fresh_uniform
#print axioms R1Z.ProverCommitAdaptiveHistory23.lazy_joint
#print axioms R1Z.ProverCommitAdaptiveHistory23.complete_joint
#print axioms R1Z.ProverCommitPolicy23.roundtrip
#print axioms R1Z.ProverCommitPolicy23.sample_total
#print axioms R1Z.ProverCommitPolicy23.installed_total
#print axioms R1Z.ProverCommitPolicy23.rho_caller
#print axioms R1Z.ProverCommitPolicy23.rho_after_block
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
#print axioms R1Z.PrivacyR1HeadlineDeployed.privacy_headline_deployed
#print axioms AspisV8R19.MemoizedProgramLaw.empty_oracle_law
#print axioms R1Z.QueryScanFreshProgram.fresh_oracle_bound

import R1Z.ProverRwFullAudit
import R1Z.ProverRwCallerBinding
import R1Z.ProverRwSaltLoop
import R1Z.ProverRwEntropyIteration

/-! New continuation obligations and the proved obstruction. The earlier
full caller audit is reused; no release or full-manifest result is asserted. -/
#check @R1Z.ProverRwCallerBinding.eight
#check @R1Z.ProverRwEntropyIteration.no_retry_then_success
#print axioms R1Z.ProverRwCallerBinding.variant_exact
#print axioms R1Z.ProverRwCallerBinding.admitted
#print axioms R1Z.ProverRwCallerBinding.rejected_variant
#print axioms R1Z.ProverRwCallerBinding.eight
#print axioms R1Z.ProverRwSaltLoop.loop_finite
#print axioms R1Z.ProverRwSaltLoop.error_suffix
#print axioms R1Z.ProverRwSaltLoop.finite_eager
#print axioms R1Z.ProverRwSaltLoop.loop_eager
#print axioms R1Z.ProverRwEntropyObstruction.distinct
#print axioms R1Z.ProverRwEntropyObstruction.no_two_draw_dictionary
#print axioms R1Z.ProverRwEntropyObstruction.effectful_two_draws
#print axioms R1Z.ProverRwEntropyIteration.same_iteration_shape
#print axioms R1Z.ProverRwEntropyIteration.no_retry_then_success

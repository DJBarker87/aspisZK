import R1Z.SimCostLazyBytes
import R1Z.SimCostFixedOperations
import R1Z.SimCostLazyBoundedBytes
import R1Z.PrivacyR1HeadlineV2SimProto

/-! Final assembly audit of the independent cost stages and retained headline.
No unconditional full-preparation certificate is asserted. -/
#print axioms R1Z.SimCostLazyBytes.cons_lookup
#print axioms R1Z.SimCostLazyBytes.run_erase
#print axioms R1Z.SimCostLazyBytes.run_bound
#print axioms R1Z.SimCostLazyBytes.addresses_mono
#print axioms R1Z.SimCostLazyBytes.addresses_bytes
#print axioms R1Z.SimCostLazyBytes.run_relative
#print axioms R1Z.SimCostFixedOperations.batch_erase
#print axioms R1Z.SimCostFixedOperations.batch_bound
#print axioms R1Z.SimCostFixedOperations.m31_add_batch
#print axioms R1Z.SimCostFixedOperations.m31_mul_batch
#print axioms R1Z.SimCostFixedOperations.qm31_add_batch
#print axioms R1Z.SimCostFixedOperations.qm31_mul_batch
#print axioms R1Z.SimCostFixedOperations.protocol_sized_batch
#print axioms R1Z.SimCostLazyBoundedBytes.initial_cons
#print axioms R1Z.SimCostLazyBoundedBytes.run_erase
#print axioms R1Z.SimCostLazyBoundedBytes.run_bound
#print axioms R1Z.SimCostLazyBoundedBytes.run_relative
#print axioms R1Z.SimCostLazyBoundedBytes.uniform
#print axioms R1Z.SimCostLazyBoundedBytes.protocol_relative
#print axioms R1Z.SimCostLazyBoundedBytes.protocol_uniform
#print axioms R1Z.SimCostFixedOperations.m31Add
#print axioms R1Z.SimCostFixedOperations.m31Mul
#print axioms R1Z.SimCostFixedOperations.qm31Add
#print axioms R1Z.SimCostFixedOperations.qm31Mul
#print axioms R1Z.SimCostFixedOperations.fixedBatch
#print axioms R1Z.SimCostTapeCoupling.sample_count
#print axioms R1Z.SimCostTapeCoupling.tape_source_draws
#print axioms R1Z.PrivacyR1HeadlineV2SimProto.privacy_headline_v2_sim_proto

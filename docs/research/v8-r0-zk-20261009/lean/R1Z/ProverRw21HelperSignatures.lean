import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.ProverRw21HelperSignatures
open ProverRwFull
-- Focused signature inventory for splitting the helper-mode dictionary proof.
#check @host_semantic.check_semantic_columns
#check @host_wire.SemanticTranscript.new
#check @host_semantic.semantic_row
#check @host_semantic.lift_columns
#check @host_semantic.zc_rows
#check @host_semantic.add_d_tail
#check @host_semantic.initial_mask_sum
#check @host_semantic.point_claims
#check @host_semantic.extra_claims
#check @host_semantic.claim_bytes
#check @host_semantic.endpoint_bytes
#check @host_sumcheck.prove_sumcheck
#check @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
#check @host_semantic.build_with_helper_mode.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
#check @host_semantic.build_with_helper_mode.closure_1.Insts.CoreOpsFunctionFnOnceTupleStateOnlyMaskBuildErrorError
end R1Z.ProverRw21HelperSignatures

import OraclePortCkptAbi5Decision
import OraclePortCkptAbi5Codec
import OraclePortCkptAbi5Weights
import OraclePortCkptAbi5Reached

/-! Focused compatible union and standard-axiom audit. This is not a full
frozen release replay or an instantiated Rust AcceptedRunJoin. -/
#print axioms AspisR1.OraclePortCkptAbi5Stage.stage_observation
#print axioms AspisR1.OraclePortCkptAbi5Stage.reached_stage
#print axioms AspisR1.OraclePortCkptAbi5Decision.after_observation
#print axioms AspisR1.OraclePortCkptAbi5Decision.decision_observation
#print axioms AspisR1.OraclePortCkptAbi5Codec.c5_k_bytes
#print axioms AspisR1.OraclePortCkptAbi5Codec.c5_wide_halves
#print axioms AspisR1.OraclePortCkptAbi5Codec.c5_e_bytes
#print axioms AspisR1.OraclePortCkptAbi5Codec.decoded_k_bytes
#print axioms AspisR1.OraclePortCkptAbi5Codec.decoded_e_bytes
#print axioms AspisR1.OraclePortCkptAbi5Weights.overwrite_exact
#print axioms AspisR1.OraclePortCkptAbi5Weights.allocated_overwrite_exact
#print axioms AspisR1.OraclePortCkptAbi5Reached.chain_endpoint
#print axioms AspisR1.OraclePortCkptAbi5Reached.successful_chain
#print axioms AspisR1.OraclePortCkptAbi5Reached.emitted_body
#print axioms AspisR1.OraclePortCkptAbi5Reached.reached_calls
#print axioms AspisR1.OraclePortCkptAbi5Reached.tx1_next
#print axioms AspisR1.OraclePortCkptAbi5Reached.tx2_next
#print axioms AspisR1.OraclePortStdAllocation.filled_exact

import S2W_SuccessOracle
import S2W_EntryWriteHistory
import S2W_ChildJoins
import S2W_Observation

/-! Focused final union. There is no native S2CallerFacts constructor here:
projected wrappers and opaque child source event ports remain separate. -/
#print axioms AspisR1.S2W_LeadInterface.proof_suffix_bytes
#print axioms AspisR1.S2W_LeadInterface.checkpoint_oracle
#print axioms AspisR1.S2W_LeadInterface.checkpoint_binding
#print axioms AspisR1.S2W_LeadInterface.compose
#print axioms AspisR1.S2W_LeadInterface.multiproof_join
#print axioms AspisR1.S2W_LeadInterface.y1_join
#print axioms AspisR1.S2W_SuccessOracle.returned_raw
#print axioms AspisR1.S2W_SuccessOracle.native_success_field
#print axioms AspisR1.S2W_SuccessOracle.before_to_after
#print axioms AspisR1.S2W_SuccessOracle.masked_success
#print axioms AspisR1.S2W_WrapperLaws.copy_projection
#print axioms AspisR1.S2W_WrapperLaws.lift_projection
#print axioms AspisR1.S2W_WrapperLaws.native_snapshot_protocol
#print axioms AspisR1.S2W_WrapperLaws.write_bracket
#print axioms AspisR1.S2W_WrapperLaws.checkpoint_write
#print axioms AspisR1.S2W_WrapperLaws.trusted_write_protocol
#print axioms AspisR1.S2W_EntryWriteHistory.written_bytes
#print axioms AspisR1.S2W_EntryWriteHistory.entry_write_history
#print axioms AspisR1.S2W_ChildJoins.internal_geometry
#print axioms AspisR1.S2W_Observation.accepted_observation
#print axioms AspisR1.S2W_Observation.accepted_segments
#print AspisR1.S2W_EntryWriteHistory.entry_write_history
#print AspisR1.S2W_WrapperLaws.native_snapshot_protocol
#print AspisR1.S2W_WrapperLaws.trusted_write_protocol
#print AspisR1.S2W_LeadInterface.S2CallerFacts

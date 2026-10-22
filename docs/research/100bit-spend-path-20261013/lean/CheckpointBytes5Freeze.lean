import CheckpointBytes5Decision

/-! One final focused union/axioms audit; no frozen release replay claim. -/

#print axioms AspisR1.CheckpointBytes5Decision.bindObservation_eval
#print axioms AspisR1.CheckpointBytes5Decision.decision_success_join
#print axioms AspisR1.CheckpointBytes5Effect.bind_run
#print axioms AspisR1.CheckpointBytes5Effect.erase_bind
#print axioms AspisR1.CheckpointBytes5Effect.erase_lift
#print axioms AspisR1.CheckpointBytes5Effect.erase_read
#print axioms AspisR1.CheckpointBytes5Effect.erase_pure
#print axioms AspisR1.CheckpointBytes5Effect.run_success
#print axioms AspisR1.CheckpointBytes5Effect.run_bind
#print axioms AspisR1.CheckpointBytes5Effect.run_lift
#print axioms AspisR1.CheckpointBytes5Effect.run_read
#print axioms AspisR1.CheckpointBytes5Effect.run_pure
#print axioms AspisR1.CheckpointBytes5Effect.erase_ite
#print axioms AspisR1.CheckpointBytes5Effect.run_ite
#print axioms AspisR1.CheckpointBytes5Inputs.singleton_input
#print axioms AspisR1.CheckpointBytes5Inputs.checksum_input
#print axioms AspisR1.CheckpointBytes5Inputs.calls_inputs
#print axioms AspisR1.CheckpointBytes5Inputs.calls_observation
#print axioms AspisR1.CheckpointBytes5Join.successful_fields_and_reads
#print axioms AspisR1.CheckpointBytes5Join.error_rejects
#print axioms AspisR1.CheckpointBytes5Join.successful_stage
#print axioms AspisR1.CheckpointBytes5Join.success_conditioned_checkpoint_stage_join
#print axioms AspisR1.CheckpointBytes5Output.ofK_source
#print axioms AspisR1.CheckpointBytes5Output.ofE_source
#print axioms AspisR1.CheckpointBytes5Output.fields_observation
#print axioms AspisR1.CheckpointBytes5Resume.source
#print axioms AspisR1.CheckpointBytes5Trace.successful_log
#print axioms AspisR1.CheckpointBytes5Writer.u8_roundtrip
#print axioms AspisR1.CheckpointBytes5Writer.bytes_roundtrip
#print axioms AspisR1.CheckpointBytes5Writer.finish_bytes
#print axioms AspisR1.CheckpointBytes5Writer.writer_effects
#print axioms AspisR1.CheckpointBytes4SuccessfulFields.successful_saved_fields
#print axioms AspisR1.CheckpointBytesDecodeC5.source_body_c5
#print axioms AspisR1.OraclePortCkptAbi5Stage.reached_stage
#print axioms AspisR1.OraclePortCkptAbi5Decision.decision_observation
#print axioms AspisR1.OraclePortFrozen2Digests.six_ordered_reads

#print AspisR1.CheckpointBytes5Join.S2S10CallerBinding
#print AspisR1.CheckpointBytes5Join.S1S7S8StateProvenance
#check AspisR1.CheckpointBytes5Join.success_conditioned_checkpoint_stage_join
#check AspisR1.CheckpointBytes5Decision.decision_success_join

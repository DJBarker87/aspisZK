import R1JointActualView
import R1JointUnifiedBound

/-! Focused transcript representation and row-32 decoder checkpoint.
Global injection, all-round classification, source and privacy remain open. -/
#print axioms AspisR1.UnifiedRun.transcript_succ
#print axioms AspisR1.UnifiedRun.transcript_statement
#print axioms AspisR1.UnifiedRun.transcript_length
#print axioms AspisR1.UnifiedRun.state_succ
#print axioms AspisR1.UnifiedRun.transcript_rounds
#print axioms AspisR1.CompletedView.append_record
#print axioms AspisR1.CompletedView.singleton_record
#print axioms AspisR1.CompletedView.complete_nil
#print axioms AspisR1.JointRecoveryTotal.recover_of_seek
#print axioms AspisR1.JointRecoveryTotal.parse_recover
#print axioms AspisR1.JointRecoveryTotal.fromAnswers_has_query
#print axioms AspisR1.UnifiedPayloadValue.sampler_payload_value
#print axioms AspisR1.UnifiedRecords.records_length
#print axioms AspisR1.UnifiedRecords.records_succ
#print axioms AspisR1.UnifiedRecords.ordinary_challenge
#print axioms AspisR1.UnifiedRecordCompletion.completed_eq_transcript
#print axioms AspisR1.JointTranscriptView.view_some
#print axioms AspisR1.JointTranscriptView.follows_map
#print axioms AspisR1.JointTranscriptView.parsed_prefix_length
#print axioms AspisR1.JointUnifiedLaw.background_sampler_law
#print axioms AspisR1.UnifiedQueryRun.query_challenge
#print axioms AspisR1.UnifiedQueryRun.query_state
#print axioms AspisR1.UnifiedQueryRun.rho_address
#print axioms AspisR1.UnifiedQueryRun.rho_challenge
#print axioms AspisR1.UnifiedQueryRun.prefix32
#print axioms AspisR1.JointActualView.actual_output
#print axioms AspisR1.JointUnifiedDecoder.decode_of_parse
#print axioms AspisR1.JointUnifiedDecoder.decode_sound
#print axioms AspisR1.JointUnifiedDecoder.decoded_round
#print axioms AspisR1.JointUnifiedBound.decoded_bound

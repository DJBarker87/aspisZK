import RPx_Deployed
import NFT_STAGE2_IMPORT
import NFU_STAGE2_IMPORT
import NGC_ByteWriters
import NGC_Initialization
import NGC_FinishContents
import NGC_ValueBridge
import NGC_WriterDomain
import NGC_DigestBridge
import NGC_CheckpointBridge
import NGC_AppendFrame
import NGC_InitialInvariant
import NGC_PrestateBridge
import NGC_FillInduction
import NGC_ReferenceValues
#print axioms NGC_ByteWriters.cm
#print axioms NGC_ByteWriters.qm
#print axioms AspisR1.NGC_Initialization.heap_result
#print axioms AspisR1.NGC_Initialization.constructor
#print axioms AspisR1.NGC_Initialization.accepted
#print axioms AspisR1.NGC_Initialization.rejection
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NGC_FinishFrame.result_frame
#print axioms AspisR1.NGC_DigestBridge.observed
#print axioms AspisR1.NGC_DigestBridge.forwarding
#print axioms AspisR1.NGC_DigestBridge.checkpoint_oracle
#print axioms AspisR1.NGC_KNE_Caller.every_reached_call
#print axioms AspisR1.NGC_PreparationBoundary.canonicalK
#print axioms AspisR1.NGC_PreparationBoundary.canonicalE
#print axioms AspisR1.NGC_QueryPoststate.finite
#print axioms AspisR1.NGC_QueryPoststate.tx1
#print axioms AspisR1.NGC_WriterDomain.after_finish
#print axioms AspisR1.NGC_WriterDomain.from_query_loop
#print axioms AspisR1.NGC_LPi_SerializationFold.contents
#print axioms AspisR1.NGC_LPi_SerializationFold.byte_length
#print axioms AspisR1.NGC_LPi_SerializationFold.length
#print axioms AspisR1.NGC_LPi_SerializationFold.weights64
#print axioms AspisR1.NGC_LPm_WeightLoop.result
#print axioms AspisR1.NGC_LPm_WeightLoop.exists_trace
#print axioms AspisR1.NGC_LPm_WeightLoop.native_weights
#print axioms AspisR1.NGC_LPm_WeightLoop.reached_size
#print axioms AspisR1.NGC_LPm_WeightLoop.reached_domain
#print axioms AspisR1.NGC_LPm_CheckpointBody.source_body
#print axioms AspisR1.NGC_LPm_CheckpointBody.weights_port
#print axioms AspisR1.NGC_LPm_CheckpointProgram.materialize_eq
#print axioms AspisR1.NGC_LPm_CheckpointProgram.returned_eq
#print axioms AspisR1.NGC_LPm_CheckpointProgram.program_eq
#print axioms AspisR1.NGC_LPm_CheckpointProgram.result_and_effects
#print axioms NGC_KND_Schedule.data_independent
#print axioms NGC_KND_Schedule.exact_schedule
#print axioms NGC_KND_Schedule.append_count
#print axioms NGC_KND_Schedule.final_length
#print axioms NGC_KND_Schedule.no_growth
#print axioms NGC_KND_Schedule.body_length
#print axioms AspisR1.NGC_KNE_Model.indexed_payload
#print axioms AspisR1.NGC_KNE_Model.indexed_shape
#print axioms AspisR1.NGC_KNE_Model.flatten_ofFn
#print axioms AspisR1.NGC_KNE_Model.rawK_length
#print axioms AspisR1.NGC_KNE_Model.bodyEmissions_payload
#print axioms AspisR1.NGC_KNE_Model.bodyEmissions_shape
#print axioms AspisR1.NGC_KNE_Schedule.writer_shape
#print axioms AspisR1.NGC_KNE_Schedule.caller_final_len
#print axioms AspisR1.NGC_KNE_Schedule.derived_schedule
#print axioms AspisR1.NGC_KNE_Schedule.native_body_decomposition
#print axioms AspisR1.NGC_KNE_Schedule.returned_decomposition
#print axioms AspisR1.NGC_KNE_Composition.compose
#print axioms AspisR1.NGC_KNE_Composition.annotate_left
#print axioms AspisR1.NGC_KNE_Composition.body_entries
#print axioms AspisR1.NGC_KNE_Composition.body_bytes
#print axioms AspisR1.NGC_KNE_Writer.emission_count
#print axioms AspisR1.NGC_KNE_Writer.appendAll_eq
#print axioms AspisR1.NGC_KNE_Writer.bodyList_eq
#print axioms AspisR1.NGC_KNE_Writer.materialize_eq
#print axioms AspisR1.NGC_KNE_Writer.returnList_eq
#print axioms AspisR1.NGC_KNE_Writer.returned_eq
#print axioms AspisR1.NGC_KNE_Writer.program_eq
#print axioms AspisR1.NGC_KNE_Writer.cohort_program_eq
#print axioms AspisR1.NGC_KNE_Leaf.native_result
#print axioms AspisR1.NGC_KNE_Final.schedule_facts
#print axioms AspisR1.NGC_ValueBridge.value
#print axioms AspisR1.NGC_CheckpointBridge.derived_packet
#print axioms AspisR1.NGC_AppendFrame.bytes
#print axioms AspisR1.NGC_AppendFrame.prefix_frame
#print axioms AspisR1.NGC_AppendFrame.byte_domain
#print axioms AspisR1.NGC_AppendFrame.local_correct
#print axioms AspisR1.NGC_NFW_QueryEntry.progress
#print axioms AspisR1.NGC_NFW_QueryEntry.power
#print axioms AspisR1.NGC_NFW_QueryEntry.rhs
#print axioms AspisR1.NGC_NFW_QueryEntry.weights_canonical
#print axioms AspisR1.NGC_NFW_QueryEntry.domain
#print axioms AspisR1.NGC_FinishContents.contents
#print axioms AspisR1.NGC_InitialInvariant.initial
#print axioms AspisR1.NGC_FillInduction.result
#print axioms AspisR1.NGC_FillInduction.empty
#print axioms AspisR1.NGC_FillInduction.length
#print axioms AspisR1.NGC_FillInduction.spare_capacity
#print axioms AspisR1.NGC_ReferenceValues.resize_empty
#print axioms AspisR1.NGC_ReferenceValues.roundtrip
#print axioms AspisR1.NGC_ReferenceValues.heap
#print axioms AspisR1.NGC_ReferenceValues.finish_step
#print axioms AspisR1.NGC_PrestateBridge.from_initializers

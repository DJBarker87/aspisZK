import NLS_COMBINED_IMPORT
import NLJ_COMBINED_IMPORT
import NLC_COMBINED_IMPORT
import NLN_TX1_081
import NLV_Algebra
import NLV_All
import NLV_BatchInstall
import NLV_Continuation
import NLV_CutFold
import NLV_Deployed
import NLV_EmissionSource
import NLV_Emit_accumulator
import NLV_Emit_batch0
import NLV_Emit_checkpoint
import NLV_Emit_finishPending
import NLV_Emit_foldedCopy
import NLV_Emit_foldedSlice
import NLV_Emit_foldedUnwrap
import NLV_Emit_geometry
import NLV_Emit_guard
import NLV_Emit_markCheckpoint
import NLV_Emit_markMerkle
import NLV_Emit_markParsed
import NLV_Emit_markPrepare
import NLV_Emit_parse
import NLV_Emit_pending
import NLV_Emit_prepare
import NLV_Emit_query
import NLV_Emit_returned
import NLV_Emit_scan
import NLV_Emit_zero
import NLV_Emitted
import NLV_EvalTrace
import NLV_ExactFold
import NLV_Frame_guard
import NLV_Frames
import NLV_InitialFold
import NLV_InitialState
import NLV_Leaves
import NLV_LowerTrace
import NLV_ObservationIndex
import NLV_PairElim
import NLV_PreparePacket
import NLV_QueryCanonical
import NLV_RowSpec087
import NLV_RowSpec094
import NLV_RunLaws
import NLV_State
import NLV_Step_accumulator
import NLV_Step_batch0
import NLV_Step_checkpoint
import NLV_Step_finishPending
import NLV_Step_foldedCopy
import NLV_Step_foldedSlice
import NLV_Step_foldedUnwrap
import NLV_Step_geometry
import NLV_Step_guard
import NLV_Step_markCheckpoint
import NLV_Step_markMerkle
import NLV_Step_markParsed
import NLV_Step_markPrepare
import NLV_Step_parse
import NLV_Step_pending
import NLV_Step_prepare
import NLV_Step_query
import NLV_Step_returned
import NLV_Step_scan
import NLV_Step_zero
import NLV_Tree

-- No CLOSED094 root; parameterized support only.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLV.admission
#check @AspisR1.NLV.admission
#print axioms AspisR1.NLV.effects
#check @AspisR1.NLV.effects
#print axioms AspisR1.NLV.external_frame
#check @AspisR1.NLV.external_frame
#print axioms AspisR1.NLV.external_frame_chain
#check @AspisR1.NLV.external_frame_chain
#print axioms AspisR1.NLV.initial_admission
#check @AspisR1.NLV.initial_admission
#print axioms AspisR1.NLV.initial_external
#check @AspisR1.NLV.initial_external
#print axioms AspisR1.NLV.initial_private
#check @AspisR1.NLV.initial_private
#print axioms AspisR1.NLV.input_frame
#check @AspisR1.NLV.input_frame
#print axioms AspisR1.NLV.input_frame_chain
#check @AspisR1.NLV.input_frame_chain
#print axioms AspisR1.NLV.source_cuts
#check @AspisR1.NLV.source_cuts
#print axioms AspisR1.NLV_Algebra.assoc
#check @AspisR1.NLV_Algebra.assoc
#print axioms AspisR1.NLV_Algebra.norm_bind
#check @AspisR1.NLV_Algebra.norm_bind
#print axioms AspisR1.NLV_Algebra.right
#check @AspisR1.NLV_Algebra.right
#print axioms AspisR1.NLV_Algebra.same
#check @AspisR1.NLV_Algebra.same
#print axioms AspisR1.NLV_BatchInstall.at_call
#check @AspisR1.NLV_BatchInstall.at_call
#print axioms AspisR1.NLV_BatchInstall.event_extents
#check @AspisR1.NLV_BatchInstall.event_extents
#print axioms AspisR1.NLV_BatchInstall.event_inputs
#check @AspisR1.NLV_BatchInstall.event_inputs
#print axioms AspisR1.NLV_Deployed.dictionary
#check @AspisR1.NLV_Deployed.dictionary
#print axioms AspisR1.NLV_Deployed.digest_slot
#check @AspisR1.NLV_Deployed.digest_slot
#print axioms AspisR1.NLV_EmissionSource.source
#check @AspisR1.NLV_EmissionSource.source
#print axioms AspisR1.NLV_EmitProof.eq_accumulator
#check @AspisR1.NLV_EmitProof.eq_accumulator
#print axioms AspisR1.NLV_EmitProof.eq_batch0
#check @AspisR1.NLV_EmitProof.eq_batch0
#print axioms AspisR1.NLV_EmitProof.eq_checkpoint
#check @AspisR1.NLV_EmitProof.eq_checkpoint
#print axioms AspisR1.NLV_EmitProof.eq_finishPending
#check @AspisR1.NLV_EmitProof.eq_finishPending
#print axioms AspisR1.NLV_EmitProof.eq_foldedCopy
#check @AspisR1.NLV_EmitProof.eq_foldedCopy
#print axioms AspisR1.NLV_EmitProof.eq_foldedSlice
#check @AspisR1.NLV_EmitProof.eq_foldedSlice
#print axioms AspisR1.NLV_EmitProof.eq_foldedUnwrap
#check @AspisR1.NLV_EmitProof.eq_foldedUnwrap
#print axioms AspisR1.NLV_EmitProof.eq_geometry
#check @AspisR1.NLV_EmitProof.eq_geometry
#print axioms AspisR1.NLV_EmitProof.eq_guard
#check @AspisR1.NLV_EmitProof.eq_guard
#print axioms AspisR1.NLV_EmitProof.eq_markCheckpoint
#check @AspisR1.NLV_EmitProof.eq_markCheckpoint
#print axioms AspisR1.NLV_EmitProof.eq_markMerkle
#check @AspisR1.NLV_EmitProof.eq_markMerkle
#print axioms AspisR1.NLV_EmitProof.eq_markParsed
#check @AspisR1.NLV_EmitProof.eq_markParsed
#print axioms AspisR1.NLV_EmitProof.eq_markPrepare
#check @AspisR1.NLV_EmitProof.eq_markPrepare
#print axioms AspisR1.NLV_EmitProof.eq_parse
#check @AspisR1.NLV_EmitProof.eq_parse
#print axioms AspisR1.NLV_EmitProof.eq_pending
#check @AspisR1.NLV_EmitProof.eq_pending
#print axioms AspisR1.NLV_EmitProof.eq_prepare
#check @AspisR1.NLV_EmitProof.eq_prepare
#print axioms AspisR1.NLV_EmitProof.eq_query
#check @AspisR1.NLV_EmitProof.eq_query
#print axioms AspisR1.NLV_EmitProof.eq_returned
#check @AspisR1.NLV_EmitProof.eq_returned
#print axioms AspisR1.NLV_EmitProof.eq_scan
#check @AspisR1.NLV_EmitProof.eq_scan
#print axioms AspisR1.NLV_EmitProof.eq_zero
#check @AspisR1.NLV_EmitProof.eq_zero
#print axioms AspisR1.NLV_Emitted.try_run
#check @AspisR1.NLV_Emitted.try_run
#print axioms AspisR1.NLV_EvalTrace.exists_trace
#check @AspisR1.NLV_EvalTrace.exists_trace
#print axioms AspisR1.NLV_EvalTrace.of_run
#check @AspisR1.NLV_EvalTrace.of_run
#print axioms AspisR1.NLV_LowerTrace.source
#check @AspisR1.NLV_LowerTrace.source
#print axioms AspisR1.NLV_ObservationIndex.bound
#check @AspisR1.NLV_ObservationIndex.bound
#print axioms AspisR1.NLV_ObservationIndex.independent
#check @AspisR1.NLV_ObservationIndex.independent
#print axioms AspisR1.NLV_ObservationIndex.modulo
#check @AspisR1.NLV_ObservationIndex.modulo
#print axioms AspisR1.NLV_PairElim.elim
#check @AspisR1.NLV_PairElim.elim
#print axioms AspisR1.NLV_PreparePacket.at_call
#check @AspisR1.NLV_PreparePacket.at_call
#print axioms AspisR1.NLV_PreparePacket.full_source_cut
#check @AspisR1.NLV_PreparePacket.full_source_cut
#print axioms AspisR1.NLV_PreparePacket.source_cut
#check @AspisR1.NLV_PreparePacket.source_cut
#print axioms AspisR1.NLV_QueryCanonical.source
#check @AspisR1.NLV_QueryCanonical.source
#print axioms AspisR1.NLV_Resource087.source_projection
#check @AspisR1.NLV_Resource087.source_projection
#print axioms AspisR1.NLV_RunLaws.bind_run
#check @AspisR1.NLV_RunLaws.bind_run
#print axioms AspisR1.NLV_RunLaws.same
#check @AspisR1.NLV_RunLaws.same
#print axioms AspisR1.NLV_Tree.decrease
#check @AspisR1.NLV_Tree.decrease
#print axioms AspisR1.NLV_Tree.exact_source
#check @AspisR1.NLV_Tree.exact_source
#print axioms AspisR1.NLV_Tree.frame_accumulator
#check @AspisR1.NLV_Tree.frame_accumulator
#print axioms AspisR1.NLV_Tree.frame_batch0
#check @AspisR1.NLV_Tree.frame_batch0
#print axioms AspisR1.NLV_Tree.frame_checkpoint
#check @AspisR1.NLV_Tree.frame_checkpoint
#print axioms AspisR1.NLV_Tree.frame_finishPending
#check @AspisR1.NLV_Tree.frame_finishPending
#print axioms AspisR1.NLV_Tree.frame_foldedCopy
#check @AspisR1.NLV_Tree.frame_foldedCopy
#print axioms AspisR1.NLV_Tree.frame_foldedSlice
#check @AspisR1.NLV_Tree.frame_foldedSlice
#print axioms AspisR1.NLV_Tree.frame_foldedUnwrap
#check @AspisR1.NLV_Tree.frame_foldedUnwrap
#print axioms AspisR1.NLV_Tree.frame_geometry
#check @AspisR1.NLV_Tree.frame_geometry
#print axioms AspisR1.NLV_Tree.frame_guard
#check @AspisR1.NLV_Tree.frame_guard
#print axioms AspisR1.NLV_Tree.frame_markCheckpoint
#check @AspisR1.NLV_Tree.frame_markCheckpoint
#print axioms AspisR1.NLV_Tree.frame_markMerkle
#check @AspisR1.NLV_Tree.frame_markMerkle
#print axioms AspisR1.NLV_Tree.frame_markParsed
#check @AspisR1.NLV_Tree.frame_markParsed
#print axioms AspisR1.NLV_Tree.frame_markPrepare
#check @AspisR1.NLV_Tree.frame_markPrepare
#print axioms AspisR1.NLV_Tree.frame_parse
#check @AspisR1.NLV_Tree.frame_parse
#print axioms AspisR1.NLV_Tree.frame_pending
#check @AspisR1.NLV_Tree.frame_pending
#print axioms AspisR1.NLV_Tree.frame_prepare
#check @AspisR1.NLV_Tree.frame_prepare
#print axioms AspisR1.NLV_Tree.frame_query
#check @AspisR1.NLV_Tree.frame_query
#print axioms AspisR1.NLV_Tree.frame_returned
#check @AspisR1.NLV_Tree.frame_returned
#print axioms AspisR1.NLV_Tree.frame_scan
#check @AspisR1.NLV_Tree.frame_scan
#print axioms AspisR1.NLV_Tree.frame_zero
#check @AspisR1.NLV_Tree.frame_zero
#print axioms AspisR1.NLV_Tree.from_cuts
#check @AspisR1.NLV_Tree.from_cuts
#print axioms AspisR1.NLV_Tree.initial_source
#check @AspisR1.NLV_Tree.initial_source
#print axioms AspisR1.NLV_Tree.input_frame
#check @AspisR1.NLV_Tree.input_frame
#print axioms AspisR1.NLV_Tree.leaves_bind
#check @AspisR1.NLV_Tree.leaves_bind
#print axioms AspisR1.NLV_Tree.leaves_run
#check @AspisR1.NLV_Tree.leaves_run
#print axioms AspisR1.NLV_Tree.positive
#check @AspisR1.NLV_Tree.positive
#print axioms AspisR1.NLV_Tree.progress_accumulator
#check @AspisR1.NLV_Tree.progress_accumulator
#print axioms AspisR1.NLV_Tree.progress_batch0
#check @AspisR1.NLV_Tree.progress_batch0
#print axioms AspisR1.NLV_Tree.progress_checkpoint
#check @AspisR1.NLV_Tree.progress_checkpoint
#print axioms AspisR1.NLV_Tree.progress_finishPending
#check @AspisR1.NLV_Tree.progress_finishPending
#print axioms AspisR1.NLV_Tree.progress_foldedCopy
#check @AspisR1.NLV_Tree.progress_foldedCopy
#print axioms AspisR1.NLV_Tree.progress_foldedSlice
#check @AspisR1.NLV_Tree.progress_foldedSlice
#print axioms AspisR1.NLV_Tree.progress_foldedUnwrap
#check @AspisR1.NLV_Tree.progress_foldedUnwrap
#print axioms AspisR1.NLV_Tree.progress_geometry
#check @AspisR1.NLV_Tree.progress_geometry
#print axioms AspisR1.NLV_Tree.progress_guard
#check @AspisR1.NLV_Tree.progress_guard
#print axioms AspisR1.NLV_Tree.progress_markCheckpoint
#check @AspisR1.NLV_Tree.progress_markCheckpoint
#print axioms AspisR1.NLV_Tree.progress_markMerkle
#check @AspisR1.NLV_Tree.progress_markMerkle
#print axioms AspisR1.NLV_Tree.progress_markParsed
#check @AspisR1.NLV_Tree.progress_markParsed
#print axioms AspisR1.NLV_Tree.progress_markPrepare
#check @AspisR1.NLV_Tree.progress_markPrepare
#print axioms AspisR1.NLV_Tree.progress_parse
#check @AspisR1.NLV_Tree.progress_parse
#print axioms AspisR1.NLV_Tree.progress_pending
#check @AspisR1.NLV_Tree.progress_pending
#print axioms AspisR1.NLV_Tree.progress_prepare
#check @AspisR1.NLV_Tree.progress_prepare
#print axioms AspisR1.NLV_Tree.progress_query
#check @AspisR1.NLV_Tree.progress_query
#print axioms AspisR1.NLV_Tree.progress_returned
#check @AspisR1.NLV_Tree.progress_returned
#print axioms AspisR1.NLV_Tree.progress_scan
#check @AspisR1.NLV_Tree.progress_scan
#print axioms AspisR1.NLV_Tree.progress_zero
#check @AspisR1.NLV_Tree.progress_zero
#print axioms AspisR1.NLV_Tree.source_frame
#check @AspisR1.NLV_Tree.source_frame
#print axioms AspisR1.NLV_Tree.source_progress
#check @AspisR1.NLV_Tree.source_progress
#print axioms AspisR1.NLV_Tree.source_step
#check @AspisR1.NLV_Tree.source_step
#print axioms AspisR1.NLV_Tree.step_accumulator
#check @AspisR1.NLV_Tree.step_accumulator
#print axioms AspisR1.NLV_Tree.step_batch0
#check @AspisR1.NLV_Tree.step_batch0
#print axioms AspisR1.NLV_Tree.step_checkpoint
#check @AspisR1.NLV_Tree.step_checkpoint
#print axioms AspisR1.NLV_Tree.step_finishPending
#check @AspisR1.NLV_Tree.step_finishPending
#print axioms AspisR1.NLV_Tree.step_foldedCopy
#check @AspisR1.NLV_Tree.step_foldedCopy
#print axioms AspisR1.NLV_Tree.step_foldedSlice
#check @AspisR1.NLV_Tree.step_foldedSlice
#print axioms AspisR1.NLV_Tree.step_foldedUnwrap
#check @AspisR1.NLV_Tree.step_foldedUnwrap
#print axioms AspisR1.NLV_Tree.step_geometry
#check @AspisR1.NLV_Tree.step_geometry
#print axioms AspisR1.NLV_Tree.step_guard
#check @AspisR1.NLV_Tree.step_guard
#print axioms AspisR1.NLV_Tree.step_markCheckpoint
#check @AspisR1.NLV_Tree.step_markCheckpoint
#print axioms AspisR1.NLV_Tree.step_markMerkle
#check @AspisR1.NLV_Tree.step_markMerkle
#print axioms AspisR1.NLV_Tree.step_markParsed
#check @AspisR1.NLV_Tree.step_markParsed
#print axioms AspisR1.NLV_Tree.step_markPrepare
#check @AspisR1.NLV_Tree.step_markPrepare
#print axioms AspisR1.NLV_Tree.step_parse
#check @AspisR1.NLV_Tree.step_parse
#print axioms AspisR1.NLV_Tree.step_pending
#check @AspisR1.NLV_Tree.step_pending
#print axioms AspisR1.NLV_Tree.step_prepare
#check @AspisR1.NLV_Tree.step_prepare
#print axioms AspisR1.NLV_Tree.step_query
#check @AspisR1.NLV_Tree.step_query
#print axioms AspisR1.NLV_Tree.step_returned
#check @AspisR1.NLV_Tree.step_returned
#print axioms AspisR1.NLV_Tree.step_scan
#check @AspisR1.NLV_Tree.step_scan
#print axioms AspisR1.NLV_Tree.step_zero
#check @AspisR1.NLV_Tree.step_zero

set_option pp.proofs false
#print AspisR1.NLV_Tree.from_cuts
#print AspisR1.NLV.source_cuts

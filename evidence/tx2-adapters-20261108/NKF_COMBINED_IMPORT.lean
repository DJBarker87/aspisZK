import NKC_COMBINED_IMPORT
import NKF_BoxModel
import NKF_MasterBox
import NKF_CheckpointBox
import NKF_BoxInstall
import NKF_ArrayFrame
import NKF_BoxFields
import NKF_Windows
import NKF_Roots
import NKF_LaneTrace
import NKF_PdaModel

#check AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
#check NKF_BoxModel.box_value
#print axioms NKF_BoxModel.box_value
#check NKF_BoxModel.error
#print axioms NKF_BoxModel.error
#check NKF_BoxModel.success
#print axioms NKF_BoxModel.success
#check NKF_BoxModel.abort
#print axioms NKF_BoxModel.abort
#check NKF_BoxModel.diverge
#print axioms NKF_BoxModel.diverge
#check NKF_BoxModel.congruence
#print axioms NKF_BoxModel.congruence
#check NKF_MasterBox.raw_child
#print axioms NKF_MasterBox.raw_child
#check NKF_MasterBox.source
#print axioms NKF_MasterBox.source
#check NKF_CheckpointBox.raw_child
#print axioms NKF_CheckpointBox.raw_child
#check NKF_CheckpointBox.source
#print axioms NKF_CheckpointBox.source
#check NKF_BoxInstall.actual_slots
#print axioms NKF_BoxInstall.actual_slots
#check NKF_BoxInstall.digest_error_frame
#print axioms NKF_BoxInstall.digest_error_frame
#check NKF_ArrayFrame.array_ext
#print axioms NKF_ArrayFrame.array_ext
#check NKF_ArrayFrame.point_frame
#print axioms NKF_ArrayFrame.point_frame
#check NKF_BoxFields.master
#print axioms NKF_BoxFields.master
#check NKF_BoxFields.checkpoint
#print axioms NKF_BoxFields.checkpoint
#check NKF_Windows.bounded_cells
#print axioms NKF_Windows.bounded_cells
#check NKF_Windows.word_cells
#print axioms NKF_Windows.word_cells
#check NKF_Windows.master_fields
#print axioms NKF_Windows.master_fields
#check NKF_Windows.checkpoint_fields
#print axioms NKF_Windows.checkpoint_fields
#check NKF_Roots.master_tail
#print axioms NKF_Roots.master_tail
#check NKF_Roots.checkpoint_tail
#print axioms NKF_Roots.checkpoint_tail
#check NKF_Roots.master
#print axioms NKF_Roots.master
#check NKF_Roots.checkpoint
#print axioms NKF_Roots.checkpoint
#check NKF_LaneTrace.iteration_frame
#print axioms NKF_LaneTrace.iteration_frame
#check NKF_LaneTrace.error_no_write
#print axioms NKF_LaneTrace.error_no_write
#check NKF_LaneTrace.rejected_write
#print axioms NKF_LaneTrace.rejected_write
#check NKF_LaneTrace.loop_frame
#print axioms NKF_LaneTrace.loop_frame
#check NKF_LaneTrace.abort_no_suffix
#print axioms NKF_LaneTrace.abort_no_suffix
#check NKF_PdaModel.success
#print axioms NKF_PdaModel.success
#check NKF_PdaModel.error
#print axioms NKF_PdaModel.error
#check NKF_PdaModel.abort
#print axioms NKF_PdaModel.abort
#check NKF_PdaModel.divergence
#print axioms NKF_PdaModel.divergence
#check NKF_PdaModel.no_suffix
#print axioms NKF_PdaModel.no_suffix

set_option pp.proofs false in
#print NKF_Roots.MasterCut

set_option pp.proofs false in
#print NKF_Roots.CheckpointCut

set_option pp.proofs false in
#print NKF_Roots.MasterTail

set_option pp.proofs false in
#print NKF_Roots.CheckpointTail

set_option pp.proofs false in
#print NKF_BoxFields.Master

set_option pp.proofs false in
#print NKF_BoxFields.Checkpoint

set_option pp.proofs false in
#print NKF_Windows.Master

set_option pp.proofs false in
#print NKF_Windows.Checkpoint

set_option pp.proofs false in
#print NKF_Roots.master

set_option pp.proofs false in
#print NKF_Roots.checkpoint

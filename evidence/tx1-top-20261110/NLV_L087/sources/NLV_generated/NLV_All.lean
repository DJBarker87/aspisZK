import NLV_Frames
import NLV_Step_guard
import NLV_Frame_guard
import NLV_Step_parse
import NLV_Step_scan
import NLV_Step_markParsed
import NLV_Step_zero
import NLV_Step_prepare
import NLV_Step_accumulator
import NLV_Step_markPrepare
import NLV_Step_foldedSlice
import NLV_Step_foldedCopy
import NLV_Step_foldedUnwrap
import NLV_Step_batch0
import NLV_Step_markMerkle
import NLV_Step_geometry
import NLV_Step_pending
import NLV_Step_query
import NLV_Step_finishPending
import NLV_Step_checkpoint
import NLV_Step_markCheckpoint
import NLV_Step_returned
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem source_step (cfg : Configuration) (s : NLJ_Tx1.State) :
 CheckpointBytes5Effect.bind (step cfg s) (continuation cfg)=denote cfg s := by
 cases s with
 | mk i l =>
   cases l with
   | guard => exact step_guard cfg i
   | parse => exact step_parse cfg i
   | scan => exact step_scan cfg i
   | markParsed => exact step_markParsed cfg i
   | zero => exact step_zero cfg i
   | prepare g => exact step_prepare cfg i g
   | accumulator g p => exact step_accumulator cfg i g p
   | markPrepare g p a => exact step_markPrepare cfg i g p a
   | foldedSlice g p a => exact step_foldedSlice cfg i g p a
   | foldedCopy g p a slice => exact step_foldedCopy cfg i g p a slice
   | foldedUnwrap g p a r => exact step_foldedUnwrap cfg i g p a r
   | batch0 g p a root => exact step_batch0 cfg i g p a root
   | markMerkle g p a => exact step_markMerkle cfg i g p a
   | geometry g p a => exact step_geometry cfg i g p a
   | pending g p a geom => exact step_pending cfg i g p a geom
   | query g p a geom pending => exact step_query cfg i g p a geom pending
   | finishPending p a pending => exact step_finishPending cfg i p a pending
   | checkpoint p a => exact step_checkpoint cfg i p a
   | markCheckpoint bytes => exact step_markCheckpoint cfg i bytes
   | returned bytes => exact step_returned cfg i bytes
theorem source_frame (cfg : Configuration) (s : NLJ_Tx1.State) :
 AllLeaves (FramePost s) (step cfg s) := by
 cases s with
 | mk i l =>
   cases l with
   | guard => exact frame_guard cfg i
   | parse => exact frame_parse cfg i
   | scan => exact frame_scan cfg i
   | markParsed => exact frame_markParsed cfg i
   | zero => exact frame_zero cfg i
   | prepare g => exact frame_prepare cfg i g
   | accumulator g p => exact frame_accumulator cfg i g p
   | markPrepare g p a => exact frame_markPrepare cfg i g p a
   | foldedSlice g p a => exact frame_foldedSlice cfg i g p a
   | foldedCopy g p a slice => exact frame_foldedCopy cfg i g p a slice
   | foldedUnwrap g p a r => exact frame_foldedUnwrap cfg i g p a r
   | batch0 g p a root => exact frame_batch0 cfg i g p a root
   | markMerkle g p a => exact frame_markMerkle cfg i g p a
   | geometry g p a => exact frame_geometry cfg i g p a
   | pending g p a geom => exact frame_pending cfg i g p a geom
   | query g p a geom pending => exact frame_query cfg i g p a geom pending
   | finishPending p a pending => exact frame_finishPending cfg i p a pending
   | checkpoint p a => exact frame_checkpoint cfg i p a
   | markCheckpoint bytes => exact frame_markCheckpoint cfg i bytes
   | returned bytes => exact frame_returned cfg i bytes
theorem source_progress (cfg : Configuration) (s : NLJ_Tx1.State) :
 AllLeaves (ProgressPost s) (step cfg s) := by
 cases s with
 | mk i l =>
   cases l with
   | guard => exact progress_guard cfg i
   | parse => exact progress_parse cfg i
   | scan => exact progress_scan cfg i
   | markParsed => exact progress_markParsed cfg i
   | zero => exact progress_zero cfg i
   | prepare g => exact progress_prepare cfg i g
   | accumulator g p => exact progress_accumulator cfg i g p
   | markPrepare g p a => exact progress_markPrepare cfg i g p a
   | foldedSlice g p a => exact progress_foldedSlice cfg i g p a
   | foldedCopy g p a slice => exact progress_foldedCopy cfg i g p a slice
   | foldedUnwrap g p a r => exact progress_foldedUnwrap cfg i g p a r
   | batch0 g p a root => exact progress_batch0 cfg i g p a root
   | markMerkle g p a => exact progress_markMerkle cfg i g p a
   | geometry g p a => exact progress_geometry cfg i g p a
   | pending g p a geom => exact progress_pending cfg i g p a geom
   | query g p a geom pending => exact progress_query cfg i g p a geom pending
   | finishPending p a pending => exact progress_finishPending cfg i p a pending
   | checkpoint p a => exact progress_checkpoint cfg i p a
   | markCheckpoint bytes => exact progress_markCheckpoint cfg i bytes
   | returned bytes => exact progress_returned cfg i bytes
theorem decrease (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (s after : NLJ_Tx1.State)
 (before log : SdkC_Source.Log)
 (returned : SdkC_Source.run h (step cfg s) before=(ok (.inr after),log)) :
 rank after<rank s := leaves_run (ProgressPost s) h (step cfg s) (source_progress cfg s) _ before log returned
theorem input_frame (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (s after : NLJ_Tx1.State)
 (before log : SdkC_Source.Log)
 (returned : SdkC_Source.run h (step cfg s) before=(ok (.inr after),log)) :
 after.input=s.input := leaves_run (FramePost s) h (step cfg s) (source_frame cfg s) _ before log returned
theorem positive (s : NLJ_Tx1.State) : 0<rank s := by
 cases s with | mk i l => cases l <;> decide
#print axioms source_step
#print axioms source_frame
#print axioms source_progress
#print axioms decrease
#print axioms input_frame
#print axioms positive
end AspisR1.NLV_Tree
end

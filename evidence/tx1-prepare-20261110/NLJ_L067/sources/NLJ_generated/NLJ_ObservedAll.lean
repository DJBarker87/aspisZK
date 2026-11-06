import NLJ_Run_parse
import NLJ_Run_mark0
import NLJ_Run_publicTranscript
import NLJ_Run_begin
import NLJ_Run_mark1
import NLJ_Run_finish
import NLJ_Frame_parse
import NLJ_Frame_mark0
import NLJ_Frame_publicTranscript
import NLJ_Frame_begin
import NLJ_Frame_mark1
import NLJ_Frame_finish
import NLJ_Progress_parse
import NLJ_Progress_mark0
import NLJ_Progress_publicTranscript
import NLJ_Progress_begin
import NLJ_Progress_mark1
import NLJ_Progress_finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
theorem run_step {H : Type} (s : State H) :
 run (PreparedHashCode.bind (step s) continuation) = run (denote s) := by
 cases s with
 | mk i locals =>
  cases locals with
  | parse => exact run_parse i
  | mark0 p => exact run_mark0 i p
  | publicTranscript p => exact run_publicTranscript i p
  | begin p t => exact run_begin i p t
  | mark1 p t c => exact run_mark1 i p t c
  | finish p t c => exact run_finish i p t c

theorem source_frame {H : Type} (s : State H) : NLC_Finish.AllLeaves (FramePost s) (step s) := by
 cases atSite : s.locals with
 | parse => exact frame_parse s atSite
 | mark0 p => exact frame_mark0 s p atSite
 | publicTranscript p => exact frame_publicTranscript s p atSite
 | begin p t => exact frame_begin s p t atSite
 | mark1 p t c => exact frame_mark1 s p t c atSite
 | finish p t c => exact frame_finish s p t c atSite

theorem source_progress {H : Type} (s : State H) : NLC_Finish.AllLeaves (ProgressPost s) (step s) := by
 cases atSite : s.locals with
 | parse => exact progress_parse s atSite
 | mark0 p => exact progress_mark0 s p atSite
 | publicTranscript p => exact progress_publicTranscript s p atSite
 | begin p t => exact progress_begin s p t atSite
 | mark1 p t c => exact progress_mark1 s p t c atSite
 | finish p t c => exact progress_finish s p t c atSite

theorem decrease {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) : rank after < rank s := by
 have actual : PreparedHashCode.erase (step s) = ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact returned
 exact NLC_Finish.all_erase (step s) (ProgressPost s) (source_progress s) (.inr after) actual

theorem input_frame {H : Type} (s after : State H)
 (returned : (run (step s)).2 = ok (.inr after)) : Frame s after := by
 have actual : PreparedHashCode.erase (step s) = ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact returned
 exact NLC_Finish.all_erase (step s) (FramePost s) (source_frame s) (.inr after) actual

theorem rank_positive {H : Type} (s : State H) : 0 < rank s := by
 cases h : s.locals <;> simp only [rank,h] <;> decide
#print axioms run_step
#print axioms source_frame
#print axioms source_progress
#print axioms decrease
#print axioms input_frame
#print axioms rank_positive
end AspisR1.NLJ_Observed
end

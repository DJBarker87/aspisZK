import NLR_PrepareRun_allocate
import NLR_PrepareRun_split
import NLR_PrepareRun_semanticRange
import NLR_PrepareRun_expandSemantic
import NLR_PrepareRun_valueRange
import NLR_PrepareRun_expandValues
import NLR_PrepareRun_rebuild
import NLR_PrepareRun_view
import NLR_PrepareRun_semantic
import NLR_PrepareRun_mapSemantic
import NLR_PrepareRun_mark
import NLR_PrepareRun_constructor
import NLR_PrepareFrame_allocate
import NLR_PrepareFrame_split
import NLR_PrepareFrame_semanticRange
import NLR_PrepareFrame_expandSemantic
import NLR_PrepareFrame_valueRange
import NLR_PrepareFrame_expandValues
import NLR_PrepareFrame_rebuild
import NLR_PrepareFrame_view
import NLR_PrepareFrame_semantic
import NLR_PrepareFrame_mapSemantic
import NLR_PrepareFrame_mark
import NLR_PrepareFrame_constructor
import NLR_PrepareProgress_allocate
import NLR_PrepareProgress_split
import NLR_PrepareProgress_semanticRange
import NLR_PrepareProgress_expandSemantic
import NLR_PrepareProgress_valueRange
import NLR_PrepareProgress_expandValues
import NLR_PrepareProgress_rebuild
import NLR_PrepareProgress_view
import NLR_PrepareProgress_semantic
import NLR_PrepareProgress_mapSemantic
import NLR_PrepareProgress_mark
import NLR_PrepareProgress_constructor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem source_run (cfg : Configuration) {H : Type} (s : State H) :
 run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) (continuation cfg)) = run (denote cfg s) := by
 cases s with
 | mk i locals =>
  cases locals with
  | allocate  => exact run_allocate cfg i 
  | split n logical => exact run_split cfg i n logical
  | semanticRange n semantic y1 splitBack vecBack => exact run_semanticRange cfg i n semantic y1 splitBack vecBack
  | expandSemantic n offY1 semantic y1 compressed splitBack vecBack => exact run_expandSemantic cfg i n offY1 semantic y1 compressed splitBack vecBack
  | valueRange n offY1 semantic y1 splitBack vecBack => exact run_valueRange cfg i n offY1 semantic y1 splitBack vecBack
  | expandValues n semantic y1 compressed splitBack vecBack => exact run_expandValues cfg i n semantic y1 compressed splitBack vecBack
  | rebuild n semantic y1 splitBack vecBack => exact run_rebuild cfg i n semantic y1 splitBack vecBack
  | view logical semantic y1 => exact run_view cfg i logical semantic y1
  | semantic logical v => exact run_semantic cfg i logical v
  | mapSemantic logical v r => exact run_mapSemantic cfg i logical v r
  | mark logical v sem => exact run_mark cfg i logical v sem
  | constructor logical v sem => exact run_constructor cfg i logical v sem
#print axioms source_run
theorem source_frame (cfg : Configuration) {H : Type} (s : State H) :
 NLC_Finish.AllLeaves (FramePost s) (step cfg s) := by
 cases atSite : s.locals with
 | allocate  => exact frame_allocate cfg s  atSite
 | split n logical => exact frame_split cfg s n logical atSite
 | semanticRange n semantic y1 splitBack vecBack => exact frame_semanticRange cfg s n semantic y1 splitBack vecBack atSite
 | expandSemantic n offY1 semantic y1 compressed splitBack vecBack => exact frame_expandSemantic cfg s n offY1 semantic y1 compressed splitBack vecBack atSite
 | valueRange n offY1 semantic y1 splitBack vecBack => exact frame_valueRange cfg s n offY1 semantic y1 splitBack vecBack atSite
 | expandValues n semantic y1 compressed splitBack vecBack => exact frame_expandValues cfg s n semantic y1 compressed splitBack vecBack atSite
 | rebuild n semantic y1 splitBack vecBack => exact frame_rebuild cfg s n semantic y1 splitBack vecBack atSite
 | view logical semantic y1 => exact frame_view cfg s logical semantic y1 atSite
 | semantic logical v => exact frame_semantic cfg s logical v atSite
 | mapSemantic logical v r => exact frame_mapSemantic cfg s logical v r atSite
 | mark logical v sem => exact frame_mark cfg s logical v sem atSite
 | constructor logical v sem => exact frame_constructor cfg s logical v sem atSite
#print axioms source_frame
theorem source_progress (cfg : Configuration) {H : Type} (s : State H) :
 NLC_Finish.AllLeaves (ProgressPost s) (step cfg s) := by
 cases atSite : s.locals with
 | allocate  => exact progress_allocate cfg s  atSite
 | split n logical => exact progress_split cfg s n logical atSite
 | semanticRange n semantic y1 splitBack vecBack => exact progress_semanticRange cfg s n semantic y1 splitBack vecBack atSite
 | expandSemantic n offY1 semantic y1 compressed splitBack vecBack => exact progress_expandSemantic cfg s n offY1 semantic y1 compressed splitBack vecBack atSite
 | valueRange n offY1 semantic y1 splitBack vecBack => exact progress_valueRange cfg s n offY1 semantic y1 splitBack vecBack atSite
 | expandValues n semantic y1 compressed splitBack vecBack => exact progress_expandValues cfg s n semantic y1 compressed splitBack vecBack atSite
 | rebuild n semantic y1 splitBack vecBack => exact progress_rebuild cfg s n semantic y1 splitBack vecBack atSite
 | view logical semantic y1 => exact progress_view cfg s logical semantic y1 atSite
 | semantic logical v => exact progress_semantic cfg s logical v atSite
 | mapSemantic logical v r => exact progress_mapSemantic cfg s logical v r atSite
 | mark logical v sem => exact progress_mark cfg s logical v sem atSite
 | constructor logical v sem => exact progress_constructor cfg s logical v sem atSite
#print axioms source_progress
theorem decrease (cfg : Configuration) {H : Type} (s after : State H)
 (returned : (run (step cfg s)).2 = ok (.inr after)) : rank after < rank s := by
 have actual : AspisR1PublicPreparation.PreparedHashCode.erase (step cfg s) = ok (.inr after) := by
  rw [←AspisR1PublicPreparation.PreparedHashCode.run_value];exact returned
 exact NLC_Finish.all_erase (step cfg s) (ProgressPost s) (source_progress cfg s) (.inr after) actual

theorem input_frame (cfg : Configuration) {H : Type} (s after : State H)
 (returned : (run (step cfg s)).2 = ok (.inr after)) : after.input=s.input := by
 have actual : AspisR1PublicPreparation.PreparedHashCode.erase (step cfg s) = ok (.inr after) := by
  rw [←AspisR1PublicPreparation.PreparedHashCode.run_value];exact returned
 exact NLC_Finish.all_erase (step cfg s) (FramePost s) (source_frame cfg s) (.inr after) actual

theorem rank_positive {H : Type} (s : State H) : 0 < rank s := by
 cases h : s.locals <;> simp only [rank,h] <;> decide
#print axioms decrease
#print axioms input_frame
#print axioms rank_positive
end AspisR1.NLR_Prepare
end

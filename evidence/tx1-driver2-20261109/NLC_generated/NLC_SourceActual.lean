import NLC_Frame_rounds
import NLC_Frame_mark2
import NLC_Frame_claims
import NLC_Frame_original
import NLC_Frame_terminal
import NLC_Frame_mapPublic
import NLC_Frame_mark3
import NLC_Frame_lowArray
import NLC_Frame_highArray
import NLC_Frame_blind
import NLC_Frame_alpha
import NLC_Frame_mask
import NLC_Frame_record25a
import NLC_Frame_decode25
import NLC_Frame_multiply
import NLC_Frame_addMask
import NLC_Frame_extra28
import NLC_Frame_addExtra
import NLC_Frame_terminalGuard
import NLC_Frame_mark4
import NLC_Frame_stateBefore
import NLC_Frame_record25b
import NLC_Frame_circle0
import NLC_Frame_record26a
import NLC_Frame_decode26
import NLC_Frame_record26b
import NLC_Frame_circle1
import NLC_Frame_mark5
import NLC_Frame_circleGuard
import NLC_Frame_payload2
import NLC_Frame_rootCopy
import NLC_Frame_verified
import NLC_Ready
import NLC_LeafSound
import NLC_Progress
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run erase)

theorem source_input_frame {H : Type} (s after : State H) 
 (returned : (run (step s)).2 = ok (.inr after)) : InputFrame s after := by
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next with
 | rounds => exact all_erase (step s) (FramePost s) (frame_rounds s atSite) (.inr after) actual
 | mark2 => exact all_erase (step s) (FramePost s) (frame_mark2 s atSite) (.inr after) actual
 | claims => exact all_erase (step s) (FramePost s) (frame_claims s atSite) (.inr after) actual
 | original => exact all_erase (step s) (FramePost s) (frame_original s atSite) (.inr after) actual
 | terminal => exact all_erase (step s) (FramePost s) (frame_terminal s atSite) (.inr after) actual
 | mapPublic => exact all_erase (step s) (FramePost s) (frame_mapPublic s atSite) (.inr after) actual
 | mark3 => exact all_erase (step s) (FramePost s) (frame_mark3 s atSite) (.inr after) actual
 | lowArray => exact all_erase (step s) (FramePost s) (frame_lowArray s atSite) (.inr after) actual
 | highArray => exact all_erase (step s) (FramePost s) (frame_highArray s atSite) (.inr after) actual
 | blind => exact all_erase (step s) (FramePost s) (frame_blind s atSite) (.inr after) actual
 | alpha => exact all_erase (step s) (FramePost s) (frame_alpha s atSite) (.inr after) actual
 | mask => exact all_erase (step s) (FramePost s) (frame_mask s atSite) (.inr after) actual
 | record25a => exact all_erase (step s) (FramePost s) (frame_record25a s atSite) (.inr after) actual
 | decode25 => exact all_erase (step s) (FramePost s) (frame_decode25 s atSite) (.inr after) actual
 | multiply => exact all_erase (step s) (FramePost s) (frame_multiply s atSite) (.inr after) actual
 | addMask => exact all_erase (step s) (FramePost s) (frame_addMask s atSite) (.inr after) actual
 | extra28 => exact all_erase (step s) (FramePost s) (frame_extra28 s atSite) (.inr after) actual
 | addExtra => exact all_erase (step s) (FramePost s) (frame_addExtra s atSite) (.inr after) actual
 | terminalGuard => exact all_erase (step s) (FramePost s) (frame_terminalGuard s atSite) (.inr after) actual
 | mark4 => exact all_erase (step s) (FramePost s) (frame_mark4 s atSite) (.inr after) actual
 | stateBefore => exact all_erase (step s) (FramePost s) (frame_stateBefore s atSite) (.inr after) actual
 | record25b => exact all_erase (step s) (FramePost s) (frame_record25b s atSite) (.inr after) actual
 | circle0 => exact all_erase (step s) (FramePost s) (frame_circle0 s atSite) (.inr after) actual
 | record26a => exact all_erase (step s) (FramePost s) (frame_record26a s atSite) (.inr after) actual
 | decode26 => exact all_erase (step s) (FramePost s) (frame_decode26 s atSite) (.inr after) actual
 | record26b => exact all_erase (step s) (FramePost s) (frame_record26b s atSite) (.inr after) actual
 | circle1 => exact all_erase (step s) (FramePost s) (frame_circle1 s atSite) (.inr after) actual
 | mark5 => exact all_erase (step s) (FramePost s) (frame_mark5 s atSite) (.inr after) actual
 | circleGuard => exact all_erase (step s) (FramePost s) (frame_circleGuard s atSite) (.inr after) actual
 | payload2 => exact all_erase (step s) (FramePost s) (frame_payload2 s atSite) (.inr after) actual
 | rootCopy => exact all_erase (step s) (FramePost s) (frame_rootCopy s atSite) (.inr after) actual
 | verified => exact all_erase (step s) (FramePost s) (frame_verified s atSite) (.inr after) actual
 | lowIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
 | highIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
#print axioms source_input_frame

theorem source_ready_next {H : Type} (s after : State H) (before : Ready s)
 (returned : (run (step s)).2 = ok (.inr after)) : Ready after := by
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next with
 | rounds => exact all_erase (step s) (ReadyPost) (ready_rounds s atSite before) (.inr after) actual
 | mark2 => exact all_erase (step s) (ReadyPost) (ready_mark2 s atSite before) (.inr after) actual
 | claims => exact all_erase (step s) (ReadyPost) (ready_claims s atSite before) (.inr after) actual
 | original => exact all_erase (step s) (ReadyPost) (ready_original s atSite before) (.inr after) actual
 | terminal => exact all_erase (step s) (ReadyPost) (ready_terminal s atSite before) (.inr after) actual
 | mapPublic => exact all_erase (step s) (ReadyPost) (ready_mapPublic s atSite before) (.inr after) actual
 | mark3 => exact all_erase (step s) (ReadyPost) (ready_mark3 s atSite before) (.inr after) actual
 | lowArray => exact all_erase (step s) (ReadyPost) (ready_lowArray s atSite before) (.inr after) actual
 | highArray => exact all_erase (step s) (ReadyPost) (ready_highArray s atSite before) (.inr after) actual
 | blind => exact all_erase (step s) (ReadyPost) (ready_blind s atSite before) (.inr after) actual
 | alpha => exact all_erase (step s) (ReadyPost) (ready_alpha s atSite before) (.inr after) actual
 | mask => exact all_erase (step s) (ReadyPost) (ready_mask s atSite before) (.inr after) actual
 | record25a => exact all_erase (step s) (ReadyPost) (ready_record25a s atSite before) (.inr after) actual
 | decode25 => exact all_erase (step s) (ReadyPost) (ready_decode25 s atSite before) (.inr after) actual
 | multiply => exact all_erase (step s) (ReadyPost) (ready_multiply s atSite before) (.inr after) actual
 | addMask => exact all_erase (step s) (ReadyPost) (ready_addMask s atSite before) (.inr after) actual
 | extra28 => exact all_erase (step s) (ReadyPost) (ready_extra28 s atSite before) (.inr after) actual
 | addExtra => exact all_erase (step s) (ReadyPost) (ready_addExtra s atSite before) (.inr after) actual
 | terminalGuard => exact all_erase (step s) (ReadyPost) (ready_terminalGuard s atSite before) (.inr after) actual
 | mark4 => exact all_erase (step s) (ReadyPost) (ready_mark4 s atSite before) (.inr after) actual
 | stateBefore => exact all_erase (step s) (ReadyPost) (ready_stateBefore s atSite before) (.inr after) actual
 | record25b => exact all_erase (step s) (ReadyPost) (ready_record25b s atSite before) (.inr after) actual
 | circle0 => exact all_erase (step s) (ReadyPost) (ready_circle0 s atSite before) (.inr after) actual
 | record26a => exact all_erase (step s) (ReadyPost) (ready_record26a s atSite before) (.inr after) actual
 | decode26 => exact all_erase (step s) (ReadyPost) (ready_decode26 s atSite before) (.inr after) actual
 | record26b => exact all_erase (step s) (ReadyPost) (ready_record26b s atSite before) (.inr after) actual
 | circle1 => exact all_erase (step s) (ReadyPost) (ready_circle1 s atSite before) (.inr after) actual
 | mark5 => exact all_erase (step s) (ReadyPost) (ready_mark5 s atSite before) (.inr after) actual
 | circleGuard => exact all_erase (step s) (ReadyPost) (ready_circleGuard s atSite before) (.inr after) actual
 | payload2 => exact all_erase (step s) (ReadyPost) (ready_payload2 s atSite before) (.inr after) actual
 | rootCopy => exact all_erase (step s) (ReadyPost) (ready_rootCopy s atSite before) (.inr after) actual
 | verified => exact all_erase (step s) (ReadyPost) (ready_verified s atSite before) (.inr after) actual
 | lowIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
 | highIndex =>
   have impossible : (fail .panic : Result (Post H)) = ok (.inr after) := by
    simpa only [step,atSite,PreparedHashCode.erase_lift] using actual
   cases impossible
#print axioms source_ready_next

def FinalPost {H : Type} : Post H → Prop
 | .inl _ => True
 | .inr _ => False

theorem verified_final {H : Type} (s : State H) (atSite : s.next = .verified) :
 AllLeaves FinalPost (step s) := by
 rw [step_verified s atSite]
 unfold window_verified
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)

def Major {H : Type} (s : State H) : Prop := rank s.next < 32

theorem source_major_next {H : Type} (s after : State H) (before : Major s)
 (returned : (run (step s)).2 = ok (.inr after)) : Major after := by
 have order := source_progress s after returned
 have actual : erase (step s) = ok (.inr after) := by
  rw [← PreparedHashCode.run_value]
  exact returned
 cases atSite : s.next
 all_goals first
 | exact False.elim (all_erase (step s) FinalPost (verified_final s atSite) (.inr after) actual)
 | (unfold Major at *;simp only [atSite,rank] at *;omega)

#print axioms verified_final
#print axioms source_major_next
end AspisR1.NLC_Finish
end

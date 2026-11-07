import NMC_SlotFrame_rounds
import NMC_SlotFrame_mark2
import NMC_SlotFrame_claims
import NMC_SlotFrame_original
import NMC_SlotFrame_terminal
import NMC_SlotFrame_mapPublic
import NMC_SlotFrame_mark3
import NMC_SlotFrame_lowArray
import NMC_SlotFrame_highArray
import NMC_SlotFrame_blind
import NMC_SlotFrame_alpha
import NMC_SlotFrame_mask
import NMC_SlotFrame_record25a
import NMC_SlotFrame_decode25
import NMC_SlotFrame_multiply
import NMC_SlotFrame_addMask
import NMC_SlotFrame_extra28
import NMC_SlotFrame_addExtra
import NMC_SlotFrame_terminalGuard
import NMC_SlotFrame_mark4
import NMC_SlotFrame_stateBefore
import NMC_SlotFrame_record25b
import NMC_SlotFrame_circle0
import NMC_SlotFrame_record26a
import NMC_SlotFrame_decode26
import NMC_SlotFrame_record26b
import NMC_SlotFrame_circle1
import NMC_SlotFrame_mark5
import NMC_SlotFrame_circleGuard
import NMC_SlotFrame_payload2
import NMC_SlotFrame_rootCopy
import NMC_SlotFrame_verified
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Complete23-slot source frame at every actual major occurrence. -/
theorem all_frames {H : Type} (s : NLC_Finish.State H) (major : Major s) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 cases atSite : s.next with
 | rounds=>exact frame_rounds s atSite
 | mark2=>exact frame_mark2 s atSite
 | claims=>exact frame_claims s atSite
 | original=>exact frame_original s atSite
 | terminal=>exact frame_terminal s atSite
 | mapPublic=>exact frame_mapPublic s atSite
 | mark3=>exact frame_mark3 s atSite
 | lowArray=>exact frame_lowArray s atSite
 | highArray=>exact frame_highArray s atSite
 | blind=>exact frame_blind s atSite
 | alpha=>exact frame_alpha s atSite
 | mask=>exact frame_mask s atSite
 | record25a=>exact frame_record25a s atSite
 | decode25=>exact frame_decode25 s atSite
 | multiply=>exact frame_multiply s atSite
 | addMask=>exact frame_addMask s atSite
 | extra28=>exact frame_extra28 s atSite
 | addExtra=>exact frame_addExtra s atSite
 | terminalGuard=>exact frame_terminalGuard s atSite
 | mark4=>exact frame_mark4 s atSite
 | stateBefore=>exact frame_stateBefore s atSite
 | record25b=>exact frame_record25b s atSite
 | circle0=>exact frame_circle0 s atSite
 | record26a=>exact frame_record26a s atSite
 | decode26=>exact frame_decode26 s atSite
 | record26b=>exact frame_record26b s atSite
 | circle1=>exact frame_circle1 s atSite
 | mark5=>exact frame_mark5 s atSite
 | circleGuard=>exact frame_circleGuard s atSite
 | payload2=>exact frame_payload2 s atSite
 | rootCopy=>exact frame_rootCopy s atSite
 | verified=>exact frame_verified s atSite
 | lowIndex=>simp only [Major,atSite,rank] at major;omega
 | highIndex=>simp only [Major,atSite,rank] at major;omega
theorem source_frame {H : Type} (s after : NLC_Finish.State H) (major : Major s)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 LocalFrame s after.locals := by
 have actual : PreparedHashCode.erase (NLC_Finish.step s)=ok (.inr after) := by
  rw [←PreparedHashCode.run_value];exact head
 exact NLC_Finish.all_erase _ _ (all_frames s major) _ actual
#print axioms all_frames
#print axioms source_frame
end AspisR1.NMC_Slots
end

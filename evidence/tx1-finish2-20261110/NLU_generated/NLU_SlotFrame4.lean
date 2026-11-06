import NLU_SlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem frame_circleGuard {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.circleGuard) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 simp only [NLC_Finish.step,atSite]
 repeat' first
 | (apply NLC_Finish.all_bind;intro)
 | (change ∀ _,_;intro)
 | (apply NLU_Slots.returned;intro;simp [LocalFrame,atSite])
 | (apply NLU_Slots.put;simp [LocalFrame,atSite])
 | exact NLU_Slots.next s _
 | (change True;trivial)
 | split
#print axioms frame_circleGuard
theorem frame_payload2 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.payload2) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 simp only [NLC_Finish.step,atSite]
 repeat' first
 | (apply NLC_Finish.all_bind;intro)
 | (change ∀ _,_;intro)
 | (apply NLU_Slots.returned;intro;simp [LocalFrame,atSite])
 | (apply NLU_Slots.put;simp [LocalFrame,atSite])
 | exact NLU_Slots.next s _
 | (change True;trivial)
 | split
#print axioms frame_payload2
theorem frame_rootCopy {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.rootCopy) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 simp only [NLC_Finish.step,atSite]
 repeat' first
 | (apply NLC_Finish.all_bind;intro)
 | (change ∀ _,_;intro)
 | (apply NLU_Slots.returned;intro;simp [LocalFrame,atSite])
 | (apply NLU_Slots.put;simp [LocalFrame,atSite])
 | exact NLU_Slots.next s _
 | (change True;trivial)
 | split
#print axioms frame_rootCopy
theorem frame_verified {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.verified) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 simp only [NLC_Finish.step,atSite]
 repeat' first
 | (apply NLC_Finish.all_bind;intro)
 | (change ∀ _,_;intro)
 | (apply NLU_Slots.returned;intro;simp [LocalFrame,atSite])
 | (apply NLU_Slots.put;simp [LocalFrame,atSite])
 | exact NLU_Slots.next s _
 | (change True;trivial)
 | split
#print axioms frame_verified
end AspisR1.NLU_Slots
end

import NLU_SlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem frame_lowArray {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.lowArray) :
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
#print axioms frame_lowArray
theorem frame_highArray {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.highArray) :
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
#print axioms frame_highArray
theorem frame_blind {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.blind) :
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
#print axioms frame_blind
theorem frame_alpha {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.alpha) :
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
#print axioms frame_alpha
theorem frame_mask {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mask) :
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
#print axioms frame_mask
theorem frame_record25a {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.record25a) :
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
#print axioms frame_record25a
theorem frame_decode25 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.decode25) :
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
#print axioms frame_decode25
end AspisR1.NLU_Slots
end

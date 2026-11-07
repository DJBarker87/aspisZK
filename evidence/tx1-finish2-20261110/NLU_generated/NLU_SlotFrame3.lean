import NLU_SlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem frame_record25b {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.record25b) :
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
#print axioms frame_record25b
theorem frame_circle0 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.circle0) :
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
#print axioms frame_circle0
theorem frame_record26a {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.record26a) :
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
#print axioms frame_record26a
theorem frame_decode26 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.decode26) :
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
#print axioms frame_decode26
theorem frame_record26b {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.record26b) :
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
#print axioms frame_record26b
theorem frame_circle1 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.circle1) :
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
#print axioms frame_circle1
theorem frame_mark5 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mark5) :
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
#print axioms frame_mark5
end AspisR1.NLU_Slots
end

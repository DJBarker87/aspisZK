import NLU_SlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem frame_multiply {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.multiply) :
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
#print axioms frame_multiply
theorem frame_addMask {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.addMask) :
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
#print axioms frame_addMask
theorem frame_extra28 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.extra28) :
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
#print axioms frame_extra28
theorem frame_addExtra {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.addExtra) :
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
#print axioms frame_addExtra
theorem frame_terminalGuard {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.terminalGuard) :
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
#print axioms frame_terminalGuard
theorem frame_mark4 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mark4) :
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
#print axioms frame_mark4
theorem frame_stateBefore {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.stateBefore) :
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
#print axioms frame_stateBefore
end AspisR1.NLU_Slots
end

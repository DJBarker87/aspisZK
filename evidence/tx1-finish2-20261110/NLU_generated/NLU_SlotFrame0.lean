import NLU_SlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem frame_rounds {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.rounds) :
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
#print axioms frame_rounds
theorem frame_mark2 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mark2) :
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
#print axioms frame_mark2
theorem frame_claims {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.claims) :
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
#print axioms frame_claims
theorem frame_original {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.original) :
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
#print axioms frame_original
theorem frame_terminal {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.terminal) :
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
#print axioms frame_terminal
theorem frame_mapPublic {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mapPublic) :
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
#print axioms frame_mapPublic
theorem frame_mark3 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.mark3) :
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
#print axioms frame_mark3
end AspisR1.NLU_Slots
end

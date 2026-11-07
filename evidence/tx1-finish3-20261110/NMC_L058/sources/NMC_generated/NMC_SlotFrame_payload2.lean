import NMC_AllSlotFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Complete local-slot frame for source occurrence payload2. The physical
native interpretation and every child effect remain separate obligations. -/
theorem frame_payload2 {H : Type} (s : NLC_Finish.State H) (atSite : s.next=.payload2) :
 AllLeaves (PostFrame s) (NLC_Finish.step s) := by
 simp only [NLC_Finish.step,atSite]
 repeat' first
 | (apply NLC_Finish.all_bind;intro)
 | (change ∀ _,_;intro)
 | (apply NMC_Slots.returned;intro;simp [LocalFrame,atSite])
 | (apply NMC_Slots.put;simp [LocalFrame,atSite])
 | exact NMC_Slots.next s _
 | (change True;trivial)
 | split
#print axioms frame_payload2
end AspisR1.NMC_Slots
end

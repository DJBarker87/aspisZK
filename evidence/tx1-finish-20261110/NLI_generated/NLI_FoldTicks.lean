import NLI_FoldPhase
import NLC_Step_mark2
import NLC_Step_mark3
import NLC_Step_original
import NLC_Step_alpha
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_FoldTicks
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
theorem mark2 (n : Nat) {H : Type} (s : State H) (site : s.next = .mark2) :
 run (fold (n+1) s) = run (fold n (setNext s .claims)) := by
 rw [fold,step_mark2 s site]
 rfl
#print axioms mark2
theorem mark3 (n : Nat) {H : Type} (s : State H) (site : s.next = .mark3) :
 run (fold (n+1) s) = run (fold n (setNext s .lowArray)) := by
 rw [fold,step_mark3 s site]
 rfl
#print axioms mark3
theorem original (n : Nat) {H : Type} (s : State H) (site : s.next = .original) :
 run (fold (n+1) s) = run (fold n (setNext s .terminal)) := by
 rw [fold,step_original s site]
 rfl
#print axioms original
theorem alpha (n : Nat) {H : Type} (s : State H) (site : s.next = .alpha) :
 run (fold (n+1) s) = run (fold n (setNext s .mask)) := by
 rw [fold,step_alpha s site]
 rfl
#print axioms alpha
end AspisR1.NLI_FoldTicks
end

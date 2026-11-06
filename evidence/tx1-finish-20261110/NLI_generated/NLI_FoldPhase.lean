import NLI_MonadNotation
import NLC_Step_mark4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_FoldPhase
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Normalize one phase tick with an abstract remaining fuel. No concrete
suffix can be unfolded while this theorem is kernel checked. -/
theorem mark4 (n : Nat) {H : Type} (s : State H) (site : s.next = .mark4) :
 run (fold (n+1) s) = run (fold n (setNext s .stateBefore)) := by
 rw [fold,step_mark4 s site]
 rfl
#print axioms mark4
end AspisR1.NLI_FoldPhase
end

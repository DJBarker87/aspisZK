import NLR_PrepareDenote
import NLJ_PrepareWindow_split
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem progress_split  (cfg : Configuration) {H : Type} (s : State H) (n : Usize) (logical : alloc.vec.Vec U8)
 (atSite : s.locals = .split n logical) : NLC_Finish.AllLeaves (ProgressPost s) (step cfg s) := by
 rw [step_split cfg s n logical atSite]
 unfold window_split
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals change rank _ < rank s
 all_goals simp only [rank,advance,atSite]
 all_goals decide
#print axioms progress_split
end AspisR1.NLR_Prepare
end

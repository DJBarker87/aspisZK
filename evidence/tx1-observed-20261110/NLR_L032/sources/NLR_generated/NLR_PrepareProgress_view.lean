import NLR_PrepareDenote
import NLJ_PrepareWindow_view
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem progress_view  (cfg : Configuration) {H : Type} (s : State H) (logical : alloc.vec.Vec U8) (semantic y1 : Slice U8)
 (atSite : s.locals = .view logical semantic y1) : NLC_Finish.AllLeaves (ProgressPost s) (step cfg s) := by
 rw [step_view cfg s logical semantic y1 atSite]
 unfold window_view
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals change rank _ < rank s
 all_goals simp only [rank,advance,atSite]
 all_goals decide
#print axioms progress_view
end AspisR1.NLR_Prepare
end

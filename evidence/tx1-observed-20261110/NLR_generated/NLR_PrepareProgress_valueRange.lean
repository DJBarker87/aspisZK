import NLR_PrepareDenote
import NLJ_PrepareWindow_valueRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
open NLJ_Prepare
theorem progress_valueRange  (cfg : Configuration) {H : Type} (s : State H) (n offY1 : Usize) (semantic y1 : Slice U8) (splitBack : SplitBack) (vecBack : VecBack)
 (atSite : s.locals = .valueRange n offY1 semantic y1 splitBack vecBack) : NLC_Finish.AllLeaves (ProgressPost s) (step cfg s) := by
 rw [step_valueRange cfg s n offY1 semantic y1 splitBack vecBack atSite]
 unfold window_valueRange
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals change rank _ < rank s
 all_goals simp only [rank,advance,atSite]
 all_goals decide
#print axioms progress_valueRange
end AspisR1.NLR_Prepare
end

import NLJ_ObservedInvariants
import NLJ_Occurrence_parse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Arbitrary-reply progress for this source occurrence, not a native cut. -/
theorem progress_parse {H : Type} (s : State H)
 (atSite : s.locals = .parse) : NLC_Finish.AllLeaves (ProgressPost s) (step s) := by
 rw [occurrence_parse s  atSite]
 unfold parseWindow
 repeat' first
 | (apply NLC_Finish.all_bind; intro)
 | (change ∀ _, _; intro)
 | (change True; trivial)
 | split
 all_goals change rank _ < rank s
 all_goals simp only [rank,advance,atSite]
 all_goals decide
#print axioms progress_parse
end AspisR1.NLJ_Observed
end

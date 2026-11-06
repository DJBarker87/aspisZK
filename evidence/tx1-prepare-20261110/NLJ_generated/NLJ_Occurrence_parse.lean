import NLJ_ObservedWindows
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- One exact source occurrence. Native carry is a separate reviewed cut. -/
theorem occurrence_parse {H : Type} (s : State H)
 (atSite : s.locals = .parse) : step s = parseWindow s := by
 simp only [step,atSite]
 rfl
#print axioms occurrence_parse
end AspisR1.NLJ_Observed
end

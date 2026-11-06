import NLJ_ObservedDirect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
def continuation {H : Type} (post : Post H) : Code (Out H) :=
 match post with | .inl out => pure out | .inr after => denote after
end AspisR1.NLJ_Observed
end

import NLJ_PrepareState
import NLJ_ObservedState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_InstalledBoundaries
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- The actual headline std/root-copy updates retain the same fixed136
interpretation; no independently chosen child dictionary is introduced. -/
theorem finish (reservation : NP6_StdModel.Reservation) :
 S1SemanticRootCopy.install
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) (IDa_Deployed.boundaries reservation)) =
 IDa_Deployed.boundaries reservation := rfl
#print axioms finish
end AspisR1.NLJ_InstalledBoundaries
end

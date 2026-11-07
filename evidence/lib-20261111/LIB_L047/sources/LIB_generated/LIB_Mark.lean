import NHU_Mark
set_option autoImplicit false
namespace LIB_Mark
open Aeneas Aeneas.Std AspisR1PublicPreparation
/-- F8: the exact deployed emission ignores arbitrary observers, including Some.
This is an emitted-body fact, not an Option<fn>-dependent native verdict. -/
theorem result (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (i : U8) :
    VerifyPrefix.mark obs i = .ok () := rfl
theorem frame {A : Type} (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (i : U8) (next : Result A) : (do VerifyPrefix.mark obs i; next) = next := rfl
theorem effects {A : Type} (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) (i : U8)
    (next : PreparedHashCode.Code A) :
    PreparedHashCode.run (.step (VerifyPrefix.mark obs i) (fun _ => next)) =
    PreparedHashCode.run next := rfl
#print axioms result
#print axioms frame
#print axioms effects
end LIB_Mark

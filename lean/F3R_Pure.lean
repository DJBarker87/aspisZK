import F3R_Result
set_option autoImplicit false
namespace AspisR1.F3R_Pure
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

theorem erase_ok {A B : Type} (v : A) (k : A → Code B) :
    erase (AspisR1PublicPreparation.PreparedHashCode.bind (monadLift (ok v : Result A)) k)=erase (k v) := rfl

#print axioms erase_ok
end AspisR1.F3R_Pure

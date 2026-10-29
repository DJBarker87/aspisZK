import PV_B3P_DigestFields227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
theorem digest_assoc {α β γ : Type} (r : Result α) (f : α → Result β) (g : β → Result γ) :
    (r >>= f) >>= g = r >>= (fun a => f a >>= g) := by
  cases r <;> rfl
#print axioms digest_assoc
end PV_B3P_Success227

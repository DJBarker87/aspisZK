import NED_CommonValidation
set_option autoImplicit false
namespace NED_PaymentResultTransport
open Aeneas Aeneas.Std Result NED_CommonValidation

theorem map_ite {T : Type} (p : Prop) [Decidable p]
    (a b : core.result.Result T TE) :
    mapPayment (if p then a else b) = if p then mapPayment a else mapPayment b := by
  split <;> rfl

theorem outer_ok {T : Type} (r : core.result.Result T TE) :
    (do let x ← (ok r : Result (core.result.Result T TE)); ok (mapPayment x)) = ok (mapPayment r) := rfl

#print axioms map_ite
#print axioms outer_ok
end NED_PaymentResultTransport

import Mathlib.Data.Fintype.Card

/-! Cardinality transport without simplifying either finite enumeration. -/
set_option autoImplicit false
namespace AspisV8.EarlyC1InstanceTransport

theorem transport {I : Type*} (left right : Fintype I) (threshold cap : Nat)
    (margin : @Fintype.card I right + cap < 2 * threshold) :
    @Fintype.card I left + cap < 2 * threshold :=
  Eq.mpr (congrArg (fun n : Nat => n + cap < 2 * threshold)
    (@Fintype.card_congr I I left right (Equiv.refl I))) margin

#print axioms transport
end AspisV8.EarlyC1InstanceTransport

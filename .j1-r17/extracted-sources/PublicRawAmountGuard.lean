import PublicRawCore

/-! Pure amount predicates on the fixed raw carrier. This additive module leaves
the frozen serialization core unchanged. Separate 4.31/4.32 checks do not merge
kernels or establish source caller reachability. -/
set_option autoImplicit false
namespace AspisR1.PublicRawAmountGuard
open PublicRawCore

/-- The amount clause of payment validation, not its other binding checks. -/
def PaymentAmountGuard : Public → Prop
  | .transfer _ _ => True
  | .withdrawal _ amount => 0 < amount.val ∧ amount.val < 2 ^ 30

/-- The additional withdrawal option-shape fact required by checked decoding. -/
def NonzeroWithdrawal : Public → Prop
  | .transfer _ _ => True
  | .withdrawal _ amount => amount.val ≠ 0

theorem nonzero_of_payment_guard (p : Public) (h : PaymentAmountGuard p) :
    NonzeroWithdrawal p := by
  cases p with
  | transfer _ _ => trivial
  | withdrawal _ amount => exact Nat.ne_of_gt h.1

#print axioms nonzero_of_payment_guard
end AspisR1.PublicRawAmountGuard

import M31RetryFiberNatCardBridge

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

theorem natOutputFiber_card_eq_base (r : Value) :
    Nat.card (AnyOutputFiber (some r)) = Nat.card (AnyOutputFiber (some r0)) := by
  rw [natFiberCard_eq_outputFiberCard r, natFiberCard_eq_outputFiberCard r0]
  exact outputFiber_card_eq r r0

#print axioms natOutputFiber_card_eq_base

end M31RetryOutputFiber

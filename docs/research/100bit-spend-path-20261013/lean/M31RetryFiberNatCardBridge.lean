import M31RetryMassNatCard

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity

def r0 : Value := ⟨0, by decide⟩

theorem natFiberCard_eq_outputFiberCard (r : Value) :
    Nat.card (AnyOutputFiber (some r)) = outputFiberCard decode31 r := by
  letI : Fintype (outputFiber decode31 r) := outputFiberFintype decode31 r
  change Nat.card (outputFiber decode31 r) = @Fintype.card (outputFiber decode31 r)
    (outputFiberFintype decode31 r)
  exact Nat.card_eq_fintype_card

#check natFiberCard_eq_outputFiberCard
#print axioms natFiberCard_eq_outputFiberCard

end M31RetryOutputFiber

import GSByteBankAllocationM10
import BankStageLawsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSByteBankAllocationLawsM10
open AspisWideTower GSFixedInputDecoderFamily
attribute [local irreducible] GSByteBankWorkM10.run GSByteBankAllocationM10.cells

@[never_extract,noinline,irreducible] def run (coins : GSConcreteByteDecoderBank.RawCoins)
    (inputs : Inputs WideExact 5) : Option (Results WideExact 5) × Nat := GSByteBankWorkM10.run inputs coins

theorem value (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    (run coins inputs).1 = BankStageLawsM10.eager coins inputs := by
  unfold run BankStageLawsM10.eager
  exact GSByteBankWorkM10.value inputs coins

theorem work (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    (run coins inputs).2 ≤ BankStageLawsM10.budget := by
  unfold run BankStageLawsM10.budget
  exact GSByteBankWorkM10.work inputs coins

theorem invariant (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5)
    (out : Results WideExact 5) (h : (run coins inputs).1 = some out) :
    GSBankOutputEnvelopeM10.Bounded out := by
  unfold run at h
  exact GSByteBankWorkM10.bounded inputs coins out h

theorem paid (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    GSByteBankAllocationM10.cells inputs coins ≤ (run coins inputs).2 := by
  unfold run
  exact GSByteBankAllocationM10.paid inputs coins

#print axioms value
#print axioms work
#print axioms invariant
#print axioms paid
end AspisR1.GSByteBankAllocationLawsM10
end

import GSByteBankWorkM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.BankStageLawsM10
open AspisWideTower GSFixedInputDecoderFamily
attribute [local irreducible] GSByteBankWorkM10.run GSByteBankWorkM10.budget
  GSConcreteByteDecoderBank.run

@[irreducible] def run (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    Option (Results WideExact 5) × Nat := GSByteBankWorkM10.run inputs coins

@[irreducible] def eager (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    Option (Results WideExact 5) := GSConcreteByteDecoderBank.run inputs coins

@[never_extract,noinline,irreducible] def budget : Nat := GSByteBankWorkM10.budget+1

theorem value (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    (run coins inputs).1 = eager coins inputs := by
  unfold run eager
  exact GSByteBankWorkM10.value inputs coins

theorem work (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    (run coins inputs).2 ≤ budget := by
  unfold run budget
  exact GSByteBankWorkM10.work inputs coins

theorem invariant (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5)
    (out : Results WideExact 5) (ho : (run coins inputs).1 = some out) :
    GSBankOutputEnvelopeM10.Bounded out := by
  unfold run at ho
  exact GSByteBankWorkM10.bounded inputs coins out ho

#print axioms value
#print axioms work
#print axioms invariant
end AspisR1.BankStageLawsM10
end

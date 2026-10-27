import ConstantStagePackM10
import BankStageLawsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.BankStageSpecM10
open AspisWideTower GSFixedInputDecoderFamily AbstractStageSpecM10
attribute [local irreducible] GSByteBankWorkM10.run GSByteBankWorkM10.budget
  GSConcreteByteDecoderBank.run

@[irreducible] def spec (coins : GSConcreteByteDecoderBank.RawCoins) :
    StageSpec (BankStageLawsM10.eager coins) (fun _ => True)
      GSBankOutputEnvelopeM10.Bounded (fun _ => BankStageLawsM10.budget) :=
  ConstantStagePackM10.pack (BankStageLawsM10.eager coins) GSBankOutputEnvelopeM10.Bounded
    BankStageLawsM10.budget (BankStageLawsM10.run coins)
    (BankStageLawsM10.value coins) (BankStageLawsM10.work coins) (BankStageLawsM10.invariant coins)

theorem value (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    ((spec coins).run inputs).1 = BankStageLawsM10.eager coins inputs := (spec coins).value inputs

theorem work (coins : GSConcreteByteDecoderBank.RawCoins) (L : Nat) (inputs : Inputs WideExact 5) :
    ((spec coins).run inputs).2 ≤ BankStageLawsM10.budget := (spec coins).work L inputs True.intro

#print axioms value
#print axioms work
end AspisR1.BankStageSpecM10
end

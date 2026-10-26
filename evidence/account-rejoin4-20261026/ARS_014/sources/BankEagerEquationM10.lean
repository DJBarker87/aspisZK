import BankStageLawsM10

set_option autoImplicit false
namespace AspisR1.BankEagerEquationM10
open AspisWideTower GSFixedInputDecoderFamily
attribute [local irreducible] GSConcreteByteDecoderBank.run

theorem value (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    BankStageLawsM10.eager coins inputs = GSConcreteByteDecoderBank.run inputs coins := by
  unfold BankStageLawsM10.eager
  rfl

#print axioms value
end AspisR1.BankEagerEquationM10

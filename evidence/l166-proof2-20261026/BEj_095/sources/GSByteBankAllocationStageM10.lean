import GSByteBankAllocationLawsM10
import AllocationConstantStagePackM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.GSByteBankAllocationStageM10
open AspisWideTower GSFixedInputDecoderFamily
attribute [local irreducible] GSByteBankAllocationM10.cells

@[never_extract,noinline,irreducible] def spec (coins : GSConcreteByteDecoderBank.RawCoins) :=
  AllocationConstantStagePackM10.pack 1024 (BankStageLawsM10.eager coins)
    GSBankOutputEnvelopeM10.Bounded BankStageLawsM10.budget (GSByteBankAllocationLawsM10.run coins)
    (GSByteBankAllocationLawsM10.value coins) (GSByteBankAllocationLawsM10.work coins)
    (GSByteBankAllocationLawsM10.invariant coins)
    (fun inputs => GSByteBankAllocationM10.cells inputs coins) (GSByteBankAllocationLawsM10.paid coins)

theorem value (coins : GSConcreteByteDecoderBank.RawCoins) (inputs : Inputs WideExact 5) :
    ((spec coins).run inputs).1 = BankStageLawsM10.eager coins inputs := (spec coins).value inputs

#print axioms value
end AspisR1.GSByteBankAllocationStageM10
end

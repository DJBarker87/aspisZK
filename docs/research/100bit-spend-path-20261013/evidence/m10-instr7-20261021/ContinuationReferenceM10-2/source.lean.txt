import BankEagerEquationM10
import OptionReferenceTransportM10
import GSByteJointSpendExtractor

/-! Eager-reference equality only: no costed computation occurs in this
statement, so rewriting cannot traverse a concrete stage projection. -/
set_option autoImplicit false
namespace AspisR1.ContinuationReferenceM10
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
attribute [local irreducible] GSConcreteByteDecoderBank.run
  AspisWide.GSConcreteReceivedWordInputs.fromWords LiteralComputedCandidateExtract.extract
  GSByteJointSpendExtractor.decodedLists

theorem value (pub : R0P.Public AspisV8R15.ExactTowerBase.M31Exact)
    (W : Fin 29 → InitialWord WideExact) (V : Fin 5 → FinalWord WideExact)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    ((some (AspisWide.GSConcreteReceivedWordInputs.fromWords W V)).bind fun inputs =>
      (BankStageLawsM10.eager coins inputs).bind fun out =>
        LiteralComputedCandidateExtract.extract pub W (GSByteJointSpendExtractor.decodedLists W out)) =
      GSByteJointSpendExtractor.extract pub W V coins := by
  exact OptionReferenceTransportM10.value
    (AspisWide.GSConcreteReceivedWordInputs.fromWords W V)
    (BankStageLawsM10.eager coins) (fun inputs => GSConcreteByteDecoderBank.run inputs coins)
    (fun out => LiteralComputedCandidateExtract.extract pub W (GSByteJointSpendExtractor.decodedLists W out))
    (BankEagerEquationM10.value coins _)

#print axioms value
end AspisR1.ContinuationReferenceM10

import TxS_DecoderSelected
import R1LiteralMatchingFacts
import R1LiteralOpeningFunctionalFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Decoder

attribute [local irreducible] SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase TxS_Carriers.data

/-- Without any law-bearing matching-data input, the decoder either constructs
its selected semantic maps or the fixed zero maps on a rejected read. -/
theorem functional_origin (rs : LiteralAcceptanceTerminal.TranscriptRounds) :
    (∃ common : LiteralOpeningView.View,
      LiteralOpeningView.read rs=some common ∧
      (TxS_Carriers.data rs).F=SelectedOpeningFunctionals.functionals
        (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints ∧
      (TxS_Carriers.data rs).F0=SelectedOpeningFunctionals.rawBase
        (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints) ∨
    ((TxS_Carriers.data rs).F=0 ∧ (TxS_Carriers.data rs).F0=0) := by
  cases read : LiteralMatchingData.read rs with
  | none =>
    right
    simp [TxS_Carriers.data,read,TxS_Carriers.zeroData]
  | some d =>
    left
    apply TxS_DecoderSelected.selected_functionals rs
    rw [TxS_Carriers.data_of_read rs d read]
    exact read

#print axioms functional_origin
end AspisR1.TxS_Decoder
end

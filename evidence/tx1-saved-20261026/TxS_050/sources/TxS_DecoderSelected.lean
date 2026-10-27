import TxS_Carriers
import R1LiteralMatchingFacts
import R1LiteralOpeningFunctionalFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_DecoderSelected

attribute [local irreducible] SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase TxS_Carriers.data

theorem selected_functionals (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (read : LiteralMatchingData.read rs=some (TxS_Carriers.data rs)) :
    ∃ common : LiteralOpeningView.View,
      LiteralOpeningView.read rs=some common ∧
      (TxS_Carriers.data rs).F=SelectedOpeningFunctionals.functionals
        (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints ∧
      (TxS_Carriers.data rs).F0=SelectedOpeningFunctionals.rawBase
        (E := AspisWideTower.WideExact) (common.semantic.map Prod.snd) common.circlePoints := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,commonRead,
    stagedRead,row31Read,wordRead,gammaRead,kappaRead,alpha0Read,alpha1Read,contents⟩ :=
    LiteralMatchingFacts.read_success_components rs (TxS_Carriers.data rs) read
  have selected := LiteralOpeningFunctionalFacts.read_functionals rs common commonRead
  refine ⟨common,commonRead,?_,?_⟩
  · rw [contents]
    exact selected.1
  · rw [contents]
    exact selected.2

#print axioms selected_functionals
end AspisR1.TxS_DecoderSelected
end

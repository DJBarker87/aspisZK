import TxS_Carriers
import R1LiteralMatchingFacts
import R1LiteralOpeningFunctionalFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Decoder

theorem selected_functionals (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (read : LiteralMatchingData.read rs=some (TxS_Carriers.data rs)) :
    ∃ common : LiteralOpeningView.View,
      LiteralOpeningView.read rs=some common ∧
      (TxS_Carriers.data rs).F=SelectedOpeningFunctionals.functionals
        (E := LiteralTranscript.E) (common.semantic.map Prod.snd) common.circlePoints ∧
      (TxS_Carriers.data rs).F0=SelectedOpeningFunctionals.rawBase
        (E := LiteralTranscript.E) (common.semantic.map Prod.snd) common.circlePoints := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,commonRead,
    stagedRead,row31Read,wordRead,gammaRead,kappaRead,alpha0Read,alpha1Read,contents⟩ :=
    LiteralMatchingFacts.read_success_components rs (TxS_Carriers.data rs) read
  have selected := LiteralOpeningFunctionalFacts.read_functionals rs common commonRead
  refine ⟨common,commonRead,?_,?_⟩
  · rw [contents]
    exact selected.1
  · rw [contents]
    exact selected.2

/-- Without any law-bearing matching-data input, the decoder either constructs
its selected semantic maps or the fixed zero maps on a rejected read. -/
theorem functional_origin (rs : LiteralAcceptanceTerminal.TranscriptRounds) :
    (∃ common : LiteralOpeningView.View,
      LiteralOpeningView.read rs=some common ∧
      (TxS_Carriers.data rs).F=SelectedOpeningFunctionals.functionals
        (E := LiteralTranscript.E) (common.semantic.map Prod.snd) common.circlePoints ∧
      (TxS_Carriers.data rs).F0=SelectedOpeningFunctionals.rawBase
        (E := LiteralTranscript.E) (common.semantic.map Prod.snd) common.circlePoints) ∨
    ((TxS_Carriers.data rs).F=0 ∧ (TxS_Carriers.data rs).F0=0) := by
  cases read : LiteralMatchingData.read rs with
  | none =>
    right
    simp only [TxS_Carriers.data,read,Option.getD_none,TxS_Carriers.zeroData]
    exact ⟨rfl,rfl⟩
  | some d =>
    left
    apply selected_functionals rs
    rw [TxS_Carriers.data_of_read rs d read]
    exact read

#print axioms selected_functionals
#print axioms functional_origin
end AspisR1.TxS_Decoder
end

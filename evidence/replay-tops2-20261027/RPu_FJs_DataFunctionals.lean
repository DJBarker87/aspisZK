import R1LiteralMatchingSemanticData
import R1LiteralOpeningFunctionalFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_DataFunctionals
attribute [local irreducible] QuadraticAlgebra.instInv
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows
  LiteralMatchingData.read LiteralOpeningView.read

theorem values (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (d : MatchingSupport.Data AspisWideTower.WideExact) (v : LiteralOpeningView.View)
    (matching : LiteralMatchingData.read rs=some d)
    (opening : LiteralOpeningView.read rs=some v) :
    d.F=SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd) v.circlePoints ∧
    d.F0=SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd) v.circlePoints := by
  obtain ⟨common,hcommon,hW,hF,hF0⟩ := LiteralMatchingSemanticData.read_matches_view rs d matching
  have same := Option.some.inj (hcommon.symm.trans opening)
  subst common
  have funcs := LiteralOpeningFunctionalFacts.read_functionals rs v opening
  exact ⟨hF.trans funcs.1,hF0.trans funcs.2⟩

#print axioms values
end AspisR1.FJs_DataFunctionals
end

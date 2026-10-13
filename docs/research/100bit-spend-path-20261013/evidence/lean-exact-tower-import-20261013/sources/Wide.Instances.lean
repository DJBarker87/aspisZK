import Wide.Initial
import WideTower

/-! The two unchanged agreement predicates instantiated at the wide field. -/
set_option autoImplicit false
namespace AspisWide.Instances
open AspisWideTower
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces

noncomputable section

theorem wideInitialWidth29CurveDecodable :
    Width29CurveDecodable
      (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
      38229 initialBatchChallengeCap := by
  classical
  exact AspisWide.Terminal.exactV7InitialWidth29CurveDecodable (E := WideExact)

theorem wideFinalDegreeThreeCurveDecodable :
    DegreeThreeCurveDecodable
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
      9557 foldChallengeCap := by
  classical
  exact AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable (E := WideExact)

theorem unchangedChallengeCaps :
    initialBatchChallengeCap = 336869026605739 ∧
      foldChallengeCap = 9396508281246 := ⟨rfl, rfl⟩

#check @AspisWide.Terminal.exactV7InitialWidth29CurveDecodable
#check @AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable
#print axioms wideInitialWidth29CurveDecodable
#print axioms wideFinalDegreeThreeCurveDecodable
#print axioms unchangedChallengeCaps
end
end AspisWide.Instances

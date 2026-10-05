import Wide.Initial
import Wide.EncoderRegression
import AspisFormal.K1.V7ExactCorrelatedAgreementInitial

/-! Closed QM31 regressions, proved from the port through the Phase 1 encoder
identities. The final proof equalities also check that Lean identifies their
statement types with the original V7 statement types. V7 transcript-context
imports are confined to the regression files; the generic modules exclude them. -/
set_option autoImplicit false
namespace AspisWide.Regression
open AspisV5ComponentCQM31TowerExact
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces

theorem qm31InitialWidth29CurveDecodable :
    Width29CurveDecodable
      AspisPool.V7C1ConcreteProjectionBinding.exactInitialEncoder
      38229 initialBatchChallengeCap := by
  rw [← AspisWide.EncoderRegression.initialEncoder_eq_v7]
  exact AspisWide.Terminal.exactV7InitialWidth29CurveDecodable (E := QM31Exact)

theorem qm31FinalDegreeThreeCurveDecodable :
    DegreeThreeCurveDecodable
      AspisK1.V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder
      9557 foldChallengeCap := by
  rw [← AspisWide.EncoderRegression.finalEncoder_eq_v7]
  exact AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable (E := QM31Exact)

theorem initialResult_eq_v7 :
    qm31InitialWidth29CurveDecodable =
      AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialWidth29CurveDecodable :=
  Subsingleton.elim _ _

theorem finalResult_eq_v7 :
    qm31FinalDegreeThreeCurveDecodable =
      AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7FinalDegreeThreeCurveDecodable :=
  Subsingleton.elim _ _

#print axioms qm31InitialWidth29CurveDecodable
#print axioms qm31FinalDegreeThreeCurveDecodable
#print axioms initialResult_eq_v7
#print axioms finalResult_eq_v7
end AspisWide.Regression

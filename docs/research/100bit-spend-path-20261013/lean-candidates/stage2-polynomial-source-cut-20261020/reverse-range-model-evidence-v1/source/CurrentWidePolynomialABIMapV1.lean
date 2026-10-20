import AspisR1VerifierPolynomialCurrent.Types
import CurrentFinishArithmetic

set_option autoImplicit false

namespace AspisR1CurrentWide.Proof

abbrev PolyM := AspisR1VerifierPolynomialCurrent.aspis_core.field.M31
abbrev PolyCM := AspisR1VerifierPolynomialCurrent.aspis_core.field.CM31
abbrev PolyQM := AspisR1VerifierPolynomialCurrent.aspis_core.field.QM31
abbrev PolyWide := AspisR1VerifierPolynomialCurrent.aspis_core.field.WideExact

abbrev CurrentWide := E

def polyMToFinish (x : PolyM) : AspisR1FinishRelationCurrent.aspis_core.field.M31 := x
def polyCMToFinish (x : PolyCM) : FinishCM := ⟨polyMToFinish x.a, polyMToFinish x.b⟩
def polyQMToFinish (x : PolyQM) : FinishQM := ⟨polyCMToFinish x.c0, polyCMToFinish x.c1⟩
def polyWideToFinish (x : PolyWide) : AspisR1CurrentWide.Proof.FinishE :=
  ⟨polyQMToFinish x.c0, polyQMToFinish x.c1⟩
def polyWideToCurrent (x : PolyWide) : CurrentWide := ofFinishE (polyWideToFinish x)

theorem poly_m31_coordinate (x : PolyM) : polyMToFinish x = x := rfl
theorem poly_cm31_coordinates (x : PolyCM) :
    (polyCMToFinish x).a = x.a ∧ (polyCMToFinish x).b = x.b := by
  cases x
  exact ⟨rfl, rfl⟩
theorem poly_qm31_coordinates (x : PolyQM) :
    (polyQMToFinish x).c0.a = x.c0.a ∧
    (polyQMToFinish x).c0.b = x.c0.b ∧
    (polyQMToFinish x).c1.a = x.c1.a ∧
    (polyQMToFinish x).c1.b = x.c1.b := by
  cases x
  exact ⟨rfl, rfl, rfl, rfl⟩
theorem poly_wide_coordinates (x : PolyWide) :
    (polyWideToFinish x).c0.c0.a = x.c0.c0.a ∧
    (polyWideToFinish x).c0.c0.b = x.c0.c0.b ∧
    (polyWideToFinish x).c0.c1.a = x.c0.c1.a ∧
    (polyWideToFinish x).c0.c1.b = x.c0.c1.b ∧
    (polyWideToFinish x).c1.c0.a = x.c1.c0.a ∧
    (polyWideToFinish x).c1.c0.b = x.c1.c0.b ∧
    (polyWideToFinish x).c1.c1.a = x.c1.c1.a ∧
    (polyWideToFinish x).c1.c1.b = x.c1.c1.b := by
  cases x
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem poly_wide_current_coordinates (x : PolyWide) :
    (polyWideToCurrent x).c0.c0.a = x.c0.c0.a ∧
    (polyWideToCurrent x).c0.c0.b = x.c0.c0.b ∧
    (polyWideToCurrent x).c0.c1.a = x.c0.c1.a ∧
    (polyWideToCurrent x).c0.c1.b = x.c0.c1.b ∧
    (polyWideToCurrent x).c1.c0.a = x.c1.c0.a ∧
    (polyWideToCurrent x).c1.c0.b = x.c1.c0.b ∧
    (polyWideToCurrent x).c1.c1.a = x.c1.c1.a ∧
    (polyWideToCurrent x).c1.c1.b = x.c1.c1.b := by
  cases x
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms poly_m31_coordinate
#print axioms poly_cm31_coordinates
#print axioms poly_qm31_coordinates
#print axioms poly_wide_coordinates
#print axioms poly_wide_current_coordinates

end AspisR1CurrentWide.Proof

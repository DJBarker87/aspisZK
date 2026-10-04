/- Lift R40 through the retained exact deployed tower, without new field axioms. -/
import AspisV8R19.ResidualFieldLift
import AspisV8R19.WitnessNonzero
import AspisV8R15.ExactTowerBase

namespace AspisR19.QM31ResidualWitness
open AspisV8R15.ExactTowerBase RootCertificate SourceResidualPolynomial
noncomputable section

def embed : M →+* QM31Exact :=
  (algebraMap CM31Exact QM31Exact).comp (algebraMap M31Exact CM31Exact)

theorem embed_re_re (x : M) : (embed x).re.re = x := rfl

theorem embed_injective : Function.Injective embed := by
  intro x y h
  exact congrArg (fun z : QM31Exact => z.re.re) h

theorem base_half_mul_two : (half : M)*2=1 := by decide
theorem base_quarter_mul_four : (WitnessEntryData.quarter : M)*4=1 := by decide

theorem embedded_half : embed half = (2 : QM31Exact)⁻¹ := by
  have h := congrArg embed base_half_mul_two
  simp only [map_mul, map_ofNat, map_one] at h
  exact eq_inv_of_mul_eq_one_left h

theorem embedded_quarter : embed WitnessEntryData.quarter = (4 : QM31Exact)⁻¹ := by
  have h := congrArg embed base_quarter_mul_four
  simp only [map_mul, map_ofNat, map_one] at h
  exact eq_inv_of_mul_eq_one_left h

def assignment : Fin 36 → QM31Exact := fun i => embed (WitnessEntryData.assignment i)

theorem assigned_det_ne_zero :
    (assignedMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹) assignment).det ≠ 0 := by
  have h := ResidualFieldLift.assigned_det_ne_zero embed embed_injective
    half WitnessEntryData.quarter WitnessEntryData.assignment WitnessEntryData.assigned_det_ne_zero
  rw [embedded_half, embedded_quarter] at h
  exact h

theorem restricted_polynomial_ne_zero :
    (polyMinor ((2:QM31Exact)⁻¹) ((4:QM31Exact)⁻¹)).det ≠ 0 :=
  ResidualNonsingular.polynomial_nonzero _ _ assignment assigned_det_ne_zero

#print axioms embed_re_re
#print axioms embed_injective
#print axioms base_half_mul_two
#print axioms base_quarter_mul_four
#print axioms embedded_half
#print axioms embedded_quarter
#print axioms assigned_det_ne_zero
#print axioms restricted_polynomial_ne_zero
end
end AspisR19.QM31ResidualWitness

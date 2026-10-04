import AspisV8R19.R711ActivePolynomialSlice
import AspisV8R19.R712ClearedCircleEvaluation
import AspisV8R19.R713FullActiveDegree
import AspisV8R19.TwoSwapFixedRootProbability
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R714SelectedActiveNonzero
open R707FullActiveDeterminant R710SelectedActivePolynomial
open R711ActivePolynomialSlice R712ClearedCircleEvaluation R713FullActiveDegree
open MvPolynomial AspisV8R15.ExactTowerBase AspisR19.QM31ResidualWitness
noncomputable section

theorem selected_polynomial_ne_zero {F : Type*} [Field F] [Fintype F]
    (half : F) (hhalf : half ≠ 0) (h2 : (2:F) ≠ 0)
    (hcard : 429 < Fintype.card F) : (polyMinor half).det ≠ 0 := by
  have hd := full_det_degree half
  obtain ⟨u,hu,he⟩ := exists_circle_eval_ne_zero (fullMatrix half).det
    (by omega) (full_det_ne_zero half hhalf h2)
  intro hzero
  have hs := determinant_slice half u hu
  rw [hzero,map_zero] at hs
  exact he hs.symm

local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm
local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

lemma selected_half_mul_two : (embed RootCertificate.half : QM31Exact)*2=1 := by
  have h := congrArg embed base_half_mul_two
  simpa only [map_mul,map_ofNat,map_one] using h

def selectedDet : ActivePoly QM31Exact := (polyMinor (embed RootCertificate.half)).det

theorem selectedDet_ne_zero : selectedDet ≠ 0 := by
  apply selected_polynomial_ne_zero
  · intro hz
    have h := selected_half_mul_two
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  · intro hz
    have h := selected_half_mul_two
    rw [hz,mul_zero] at h
    exact zero_ne_one h
  · rw [AspisR19.TwoSwapFixedRootProbability.qm31_card]
    norm_num [P]

theorem selectedDet_degree : selectedDet.totalDegree ≤ 1070 := determinant_degree _

theorem product_domain_bad_fraction :
    ((Finset.filter (fun s => eval s selectedDet=0)
      (Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset QM31Exact)))).card : ℚ≥0) /
      ((Finset.univ : Finset QM31Exact).card^3 : ℚ≥0) ≤
        (1070 : ℚ≥0)/(Finset.univ : Finset QM31Exact).card := by
  apply (schwartz_zippel_totalDegree selectedDet_ne_zero (Finset.univ : Finset QM31Exact)).trans
  gcongr
  exact_mod_cast selectedDet_degree

theorem product_domain_bad_fraction_explicit :
    ((Finset.filter (fun s => eval s selectedDet=0)
      (Fintype.piFinset (fun _ : Fin 3 => (Finset.univ : Finset QM31Exact)))).card : ℚ≥0) /
      ((↑(P^4) : ℚ≥0)^3) ≤ (1070 : ℚ≥0)/(↑(P^4) : ℚ≥0) := by
  simpa only [Finset.card_univ,AspisR19.TwoSwapFixedRootProbability.qm31_card]
    using product_domain_bad_fraction

#print axioms selected_polynomial_ne_zero
#print axioms selected_half_mul_two
#print axioms selectedDet_ne_zero
#print axioms selectedDet_degree
#print axioms product_domain_bad_fraction
#print axioms product_domain_bad_fraction_explicit
end
end AspisV8R19.R714SelectedActiveNonzero

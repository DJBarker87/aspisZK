import AspisV8R19.R581NormalizedCorePolynomial
import AspisV8R15.ExactTowerBase
import AspisV8R19.R165QuarticExecution
import AspisV8R19.R164ProductExecution
import AspisV8R19.QM31ResidualWitness

set_option autoImplicit false
namespace AspisV8R19.R585SelectedCoreNonzero

open AspisV8R15.ExactTowerBase AspisR19.QM31ResidualWitness
open AspisV8R19.R581NormalizedCorePolynomial

noncomputable section

def selectedI : QM31Exact :=
  ⟨(⟨(0 : M31Exact), 1⟩ : CM31Exact), (0 : CM31Exact)⟩

theorem selectedI_sq : selectedI * selectedI = (-1 : QM31Exact) := by
  have hinner : (⟨(0 : M31Exact), 1⟩ : CM31Exact) ^ 2 = (-1 : CM31Exact) := by
    apply QuadraticAlgebra.ext <;>
      simp [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> rfl
  apply QuadraticAlgebra.ext
  · simpa [selectedI, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, hinner]
  · simp [selectedI, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> rfl

local instance selected_two_neZero : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have he : embed (2 : AspisR19.RootCertificate.M) = embed 0 :=
    by simpa only [map_ofNat, map_zero] using h
  have hz := embed_injective he
  exact (by decide : (2 : AspisR19.RootCertificate.M) ≠ 0) hz
⟩

theorem normalizedDet_ne_zero (half : QM31Exact) :
    (normalizedPolynomialMatrix (F := QM31Exact) half).det ≠ 0 := by
  apply normalizedPolynomialDet_ne_zero
  exact ⟨selectedI, selectedI_sq⟩

theorem normalizedDet_degree (half : QM31Exact) :
    (normalizedPolynomialMatrix (F := QM31Exact) half).det.totalDegree ≤ 1355 :=
  normalizedPolynomialDet_degree half

theorem selected_source_square :
    AspisR156FullFreeze.aspis_core.field.QM31.square
        (AspisV8R19.R164ProductExecution.encode selectedI) =
      .ok (AspisV8R19.R164ProductExecution.encode (-1 : QM31Exact)) := by
  rw [AspisV8R19.R165QuarticExecution.square, selectedI_sq]

#print axioms selectedI_sq
#print axioms normalizedDet_ne_zero
#print axioms normalizedDet_degree
#print axioms selected_source_square

end
end AspisV8R19.R585SelectedCoreNonzero

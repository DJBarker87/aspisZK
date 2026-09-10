import AspisFormal.K1.V7Tag73SecureCircleMap
import Mathlib.Data.Fintype.Card

/-! The literal secure-circle map accepts exactly QM31 minus its CM31
subfield. Singular parameters are the two embedded roots ±i and are already
excluded by that subfield test. The source's singular-first check order is
preserved; no probability, retry, or hash-freshness law is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SecureCircleParameterDomain
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7Tag73SecureCircleMap
noncomputable section

/-- The source CM31 element i, embedded in the exact QM31 tower. -/
def imaginaryUnit : QM31Exact :=
  algebraMap CM31Exact QM31Exact (QuadraticAlgebra.omega : CM31Exact)

theorem imaginaryUnit_sq : imaginaryUnit ^ 2 = -1 := by
  have inner : (QuadraticAlgebra.omega : CM31Exact)^2 = -1 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
    rfl
  unfold imaginaryUnit
  rw [← map_pow, inner, map_neg, map_one]

/-- Symbolic degree-two factorization: no field elements are enumerated. -/
theorem singular_iff (t : QM31Exact) :
    1 + t^2 = 0 ↔ t = imaginaryUnit ∨ t = -imaginaryUnit := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, imaginaryUnit_sq]
  exact add_eq_zero_iff_eq_neg'

theorem singular_im_zero (t : QM31Exact) (singular : 1+t^2=0) :
    t.im = 0 := by
  rcases (singular_iff t).mp singular with same | opposite
  · rw [same]
    exact QuadraticAlgebra.algebraMap_im _
  · rw [opposite, QuadraticAlgebra.im_neg]
    simp only [imaginaryUnit, QuadraticAlgebra.algebraMap_im, neg_zero]

theorem denominator_nonzero (t : QM31Exact) (outside : t.im ≠ 0) :
    1+t^2 ≠ 0 := fun singular => outside (singular_im_zero t singular)

/-- Acceptance of the actual source-shaped decoded-value map, including
the non-panicking inverse check before the subfield check. -/
def Admissible (t : QM31Exact) : Prop :=
  exactSecureCirclePointFromDecoded t ≠ none

theorem admissible_iff (t : QM31Exact) : Admissible t ↔ t.im ≠ 0 := by
  classical
  by_cases inSubfield : t.im = 0
  · simp only [Admissible, exactSecureCirclePointFromDecoded]
    split <;> simp [inSubfield]
  · have nonzero : 1+qm31Square t ≠ 0 := by
      simpa only [qm31Square_eq_sq, ← pow_two] using denominator_nonzero t inSubfield
    simp [Admissible, exactSecureCirclePointFromDecoded, qm31TryInv_eq,
      nonzero, inSubfield]

/-- The same characterization after literal canonical byte encoding. -/
theorem encoded_admissible_iff (t : QM31Exact) :
    exactSecureCircleParameterMap (encodeTagQM31ExactLE t) ≠ none ↔ t.im ≠ 0 := by
  simpa only [Admissible, exactSecureCircleParameterMap,
    decodeTagQM31ExactLE_encodeTagQM31ExactLE] using admissible_iff t

/-- Projection and the actual zero-imaginary embedding count the subfield;
this is not an arbitrary equivalence obtained from a cardinality oracle. -/
def zeroImaginaryEquiv : {t : QM31Exact // t.im = 0} ≃ CM31Exact where
  toFun t := t.val.re
  invFun a := ⟨⟨a,0⟩, rfl⟩
  left_inv t := by
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · rfl
    · exact t.property.symm
  right_inv _ := rfl

theorem cm31_card : Fintype.card CM31Exact = P^2 := by
  calc
    Fintype.card CM31Exact = Fintype.card (M31Exact × M31Exact) :=
      Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : M31Exact) 0)
    _ = P*P := by rw [Fintype.card_prod, ZMod.card]
    _ = P^2 := (pow_two P).symm

theorem zero_imaginary_card : Fintype.card {t : QM31Exact // t.im=0} = P^2 := by
  exact (Fintype.card_congr zeroImaginaryEquiv).trans cm31_card

noncomputable instance : Fintype {t : QM31Exact // Admissible t} := Fintype.ofFinite _

/-- Exact accepted-domain size: the singular roots are not subtracted twice. -/
theorem admissible_card :
    Fintype.card {t : QM31Exact // Admissible t} = P^4-P^2 := by
  classical
  calc
    Fintype.card {t : QM31Exact // Admissible t} =
        Fintype.card {t : QM31Exact // t.im ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquivRight admissible_iff)
    _ = Fintype.card QM31Exact - Fintype.card {t : QM31Exact // t.im=0} :=
      Fintype.card_subtype_compl (fun t : QM31Exact => t.im=0)
    _ = P^4-P^2 := by rw [qm31Exact_card, zero_imaginary_card]

#print axioms imaginaryUnit_sq
#print axioms singular_iff
#print axioms singular_im_zero
#print axioms denominator_nonzero
#print axioms admissible_iff
#print axioms encoded_admissible_iff
#print axioms cm31_card
#print axioms zero_imaginary_card
#print axioms admissible_card
end
end AspisV8.SecureCircleParameterDomain

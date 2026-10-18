import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots

open Polynomial
noncomputable section

universe u
variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]

def finiteFieldRootModulus (K : Type u) [Field K] [Fintype K] : K[X] :=
  X ^ Fintype.card K - X

def linearRootsProduct (s : Finset K) : K[X] :=
  s.prod fun a => X - C a

def CompleteRootCertificate (p : K[X]) (s : Finset K) : Prop :=
  EuclideanDomain.gcd p (finiteFieldRootModulus K) = linearRootsProduct s

theorem complete_root_certificate_iff
    (p : K[X]) (s : Finset K)
    (hcert : CompleteRootCertificate p s) (x : K) :
    IsRoot p x ↔ x ∈ s := by
  constructor
  · intro hx
    have hpx : X - C x ∣ p := Polynomial.dvd_iff_isRoot.mpr hx
    have hfx : X - C x ∣ finiteFieldRootModulus K := by
      apply Polynomial.dvd_iff_isRoot.mpr
      rw [IsRoot, finiteFieldRootModulus, eval_sub, eval_pow, eval_X]
      rw [FiniteField.pow_card]
      simp
    have hdiv : X - C x ∣ EuclideanDomain.gcd p (finiteFieldRootModulus K) :=
      EuclideanDomain.dvd_gcd hpx hfx
    rw [hcert] at hdiv
    have hprod : IsRoot (linearRootsProduct s) x :=
      Polynomial.dvd_iff_isRoot.mp hdiv
    rw [IsRoot, linearRootsProduct, eval_prod] at hprod
    simp only [eval_sub, eval_X, eval_C] at hprod
    rcases Finset.prod_eq_zero_iff.mp hprod with ⟨a, ha, hax⟩
    have hxa : x = a := sub_eq_zero.mp hax
    simpa [hxa] using ha
  · intro hx
    have hprod : IsRoot (linearRootsProduct s) x := by
      rw [IsRoot, linearRootsProduct, eval_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨x, hx, by simp⟩
    have hline : X - C x ∣ EuclideanDomain.gcd p (finiteFieldRootModulus K) := by
      rw [hcert]
      exact Polynomial.dvd_iff_isRoot.mpr hprod
    exact Polynomial.dvd_iff_isRoot.mp
      (hline.trans (EuclideanDomain.gcd_dvd_left _ _))

theorem complete_root_certificate_card_le_degree
    (p : K[X]) (hp : p ≠ 0) (s : Finset K)
    (hcert : CompleteRootCertificate p s) : s.card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  rw [Polynomial.mem_roots hp]
  exact (complete_root_certificate_iff p s hcert a).2 (Finset.mem_val.mp ha)

#print axioms complete_root_certificate_iff
#print axioms complete_root_certificate_card_le_degree

import FiniteFieldCompleteRootCertificate
import FiniteFieldModularPower

open Polynomial
noncomputable section

universe u
variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]

def finiteFieldFastRootResidue (p : K[X]) : K[X] :=
  (polynomialModPower (X : K[X]) p (Fintype.card K) - X) %ₘ p

def CompleteFastRootCertificate (p : K[X]) (s : Finset K) : Prop :=
  EuclideanDomain.gcd p (finiteFieldFastRootResidue p) = linearRootsProduct s

theorem finiteFieldFastRootResidue_eq_modulus (p : K[X]) (hp : p.Monic)
    (hdeg : (0 : WithBot Nat) < degree p) :
    finiteFieldFastRootResidue p %ₘ p = finiteFieldRootModulus K %ₘ p := by
  change ((polynomialModPower (X : K[X]) p (Fintype.card K) - X) %ₘ p) %ₘ p =
    (X ^ Fintype.card K - X) %ₘ p
  rw [(Polynomial.modByMonic_eq_self_iff hp).2
    (Polynomial.degree_modByMonic_lt _ hp)]
  rw [Polynomial.sub_modByMonic,
    polynomialModPower_remainder (X : K[X]) p hp hdeg (Fintype.card K),
    Polynomial.sub_modByMonic]

theorem fast_complete_root_certificate_iff (p : K[X]) (hp : p.Monic)
    (hdeg : (0 : WithBot Nat) < degree p) (s : Finset K)
    (hcert : CompleteFastRootCertificate p s) (x : K) :
    IsRoot p x ↔ x ∈ s := by
  constructor
  · intro hx
    have hmodroot : IsRoot (finiteFieldRootModulus K) x := by
      rw [IsRoot, finiteFieldRootModulus, eval_sub, eval_pow, eval_X]
      rw [FiniteField.pow_card]
      simp
    have hrem := finiteFieldFastRootResidue_eq_modulus p hp hdeg
    have hdivres : p ∣ finiteFieldFastRootResidue p - finiteFieldRootModulus K := by
      have hres1 : p ∣ finiteFieldFastRootResidue p %ₘ p - finiteFieldFastRootResidue p :=
        Polynomial.dvd_modByMonic_sub _ _
      have hres2 : p ∣ finiteFieldRootModulus K %ₘ p - finiteFieldRootModulus K :=
        Polynomial.dvd_modByMonic_sub _ _
      have hmid : p ∣ finiteFieldFastRootResidue p %ₘ p - finiteFieldRootModulus K %ₘ p := by
        rw [hrem]
        simpa using (dvd_zero p)
      have hres1' : p ∣ finiteFieldFastRootResidue p - finiteFieldFastRootResidue p %ₘ p := by
        have := dvd_neg.mpr hres1
        simpa only [neg_sub] using this
      have hsum :
          finiteFieldFastRootResidue p - finiteFieldRootModulus K =
            (finiteFieldFastRootResidue p - finiteFieldFastRootResidue p %ₘ p) +
              (finiteFieldFastRootResidue p %ₘ p - finiteFieldRootModulus K %ₘ p) +
              (finiteFieldRootModulus K %ₘ p - finiteFieldRootModulus K) := by ring
      rw [hsum]
      exact dvd_add (dvd_add hres1' hmid) hres2
    have hlin : X - C x ∣ p := Polynomial.dvd_iff_isRoot.mpr hx
    have hlinres : X - C x ∣ finiteFieldFastRootResidue p := by
      have hdiff := hlin.trans hdivres
      have hdiffroot : IsRoot (finiteFieldFastRootResidue p - finiteFieldRootModulus K) x :=
        Polynomial.dvd_iff_isRoot.mp hdiff
      have heval : (finiteFieldFastRootResidue p).eval x =
          (finiteFieldRootModulus K).eval x := by
        exact sub_eq_zero.mp (by simpa [IsRoot] using hdiffroot)
      apply Polynomial.dvd_iff_isRoot.mpr
      rw [IsRoot, heval]
      exact hmodroot
    have hdiv : X - C x ∣ EuclideanDomain.gcd p (finiteFieldFastRootResidue p) :=
      EuclideanDomain.dvd_gcd hlin hlinres
    rw [hcert] at hdiv
    have hprod : IsRoot (linearRootsProduct s) x := Polynomial.dvd_iff_isRoot.mp hdiv
    rw [IsRoot, linearRootsProduct, eval_prod] at hprod
    simp only [eval_sub, eval_X, eval_C] at hprod
    rcases Finset.prod_eq_zero_iff.mp hprod with ⟨a, ha, hax⟩
    have hxa : x = a := sub_eq_zero.mp hax
    simpa [hxa] using ha
  · intro hx
    have hprod : IsRoot (linearRootsProduct s) x := by
      rw [IsRoot, linearRootsProduct, eval_prod]
      exact Finset.prod_eq_zero_iff.mpr ⟨x, hx, by simp⟩
    have hline : X - C x ∣ EuclideanDomain.gcd p (finiteFieldFastRootResidue p) := by
      rw [hcert]
      exact Polynomial.dvd_iff_isRoot.mpr hprod
    exact Polynomial.dvd_iff_isRoot.mp
      (hline.trans (EuclideanDomain.gcd_dvd_left _ _))


theorem fast_complete_root_certificate_card_le_degree (p : K[X])
    (hp : p.Monic) (hdeg : (0 : WithBot Nat) < degree p)
    (s : Finset K) (hcert : CompleteFastRootCertificate p s) :
    s.card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  rw [Polynomial.mem_roots hp.ne_zero]
  exact (fast_complete_root_certificate_iff p hp hdeg s hcert a).2
    (Finset.mem_val.mp ha)

#print axioms finiteFieldFastRootResidue_eq_modulus
#print axioms fast_complete_root_certificate_iff
#print axioms fast_complete_root_certificate_card_le_degree

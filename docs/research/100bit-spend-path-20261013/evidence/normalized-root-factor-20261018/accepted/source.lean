import CantorZassenhausFastTrial
import FiniteFieldCompleteRootCertificate
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Separable

noncomputable section
namespace AspisR1.FiniteFieldNormalizedRootFactor
open Polynomial AspisR1.CantorZassenhausSplit AspisR1.CantorZassenhausFastTrial
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Bounded-degree modular power and a normalized gcd. The program takes q
explicitly; its correctness theorem supplies q = card K. -/
def rootFactor (p : K[X]) (q : Nat) : K[X] :=
  monicGCD p (polynomialModPower X p q-X)

theorem rootFactor_dvd (p : K[X]) (q : Nat) : rootFactor p q ∣ p :=
  monicGCD_dvd_left _ _

theorem rootFactor_monic (p : K[X]) (q : Nat) (hp : p ≠ 0) : (rootFactor p q).Monic :=
  monicGCD_monic _ _ hp

theorem rootFactor_roots_iff (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p) (x : K) :
    IsRoot (rootFactor p q) x ↔ IsRoot p x := by
  rw [rootFactor,monicGCD_root_iff]
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx,?_⟩
    rw [IsRoot,eval_sub,eval_X,modularPower_eval_at_root p X hp hdeg x hx q,eval_X,hq]
    simp [FiniteField.pow_card]

theorem rootFactor_dvd_frobenius (p : K[X]) (q : Nat) (hp : p.Monic)
    (hdeg : (0 : WithBot Nat)<degree p) : rootFactor p q ∣ X^q-X := by
  have hd0 : rootFactor p q ∣ polynomialModPower X p q-X := by
    unfold rootFactor monicGCD
    rw [normalize_dvd_iff]
    exact EuclideanDomain.gcd_dvd_right _ _
  have hd1 : rootFactor p q ∣ polynomialModPower X p q-X^q :=
    (rootFactor_dvd p q).trans (polynomialModPower_congruent X p hp hdeg q)
  have he : (polynomialModPower X p q-X) - (polynomialModPower X p q-X^q) = X^q-X := by ring
  rw [←he]
  exact dvd_sub hd0 hd1

theorem frobenius_separable : (X^(Fintype.card K)-X : K[X]).Separable := by
  rw [separable_def]
  convert! isCoprime_one_right.neg_right (R := K[X]) using 1
  rw [derivative_sub,derivative_X,derivative_X_pow,Nat.cast_card_eq_zero K,C_0,zero_mul,zero_sub]

theorem frobenius_splits : (X^(Fintype.card K)-X : K[X]).Splits := by
  rw [splits_iff_card_roots,FiniteField.roots_X_pow_card_sub_X,
    ←Finset.card_def,Finset.card_univ,
    FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]

theorem rootFactor_separable (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p) : (rootFactor p q).Separable := by
  subst q
  have hd := rootFactor_dvd_frobenius p (Fintype.card K) hp hdeg
  exact frobenius_separable.of_dvd hd

theorem rootFactor_splits (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p) : (rootFactor p q).Splits := by
  subst q
  have hd := rootFactor_dvd_frobenius p (Fintype.card K) hp hdeg
  exact frobenius_splits.of_dvd
    (FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card) hd

/-- An exact complete-root certificate exists for the normalized factor.
This is availability, not an executable root enumeration algorithm. -/
theorem normalized_certificate_exists (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p) :
    ∃ s : Finset K, rootFactor p q = linearRootsProduct s := by
  let g := rootFactor p q
  have hs := rootFactor_splits p q hq hp hdeg
  have hm := rootFactor_monic p q hp.ne_zero
  have hn := Polynomial.nodup_roots (rootFactor_separable p q hq hp hdeg)
  refine ⟨g.roots.toFinset,?_⟩
  change g = linearRootsProduct g.roots.toFinset
  calc
    g = (g.roots.map (X-C ·)).prod := hs.eq_prod_roots_of_monic hm
    _ = linearRootsProduct g.roots.toFinset := by
      unfold linearRootsProduct
      change (g.roots.map (X-C ·)).prod =
        (g.roots.toFinset.val.map (X-C ·)).prod
      rw [Multiset.toFinset_val,Multiset.dedup_eq_self.mpr hn]

def NormalizedCompleteRootCertificate (p : K[X]) (q : Nat) (s : Finset K) : Prop :=
  rootFactor p q = linearRootsProduct s

theorem normalized_certificate_iff (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p)
    (s : Finset K) (hs : NormalizedCompleteRootCertificate p q s) (x : K) :
    IsRoot p x ↔ x ∈ s := by
  rw [←rootFactor_roots_iff p q hq hp hdeg x]
  change IsRoot (rootFactor p q) x ↔ x ∈ s
  rw [hs]
  simp only [IsRoot,linearRootsProduct,eval_prod,eval_sub,eval_X,eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a,ha,hxa⟩
    have he : x=a := sub_eq_zero.mp hxa
    simpa [he] using ha
  · intro hx
    exact ⟨x,hx,sub_self x⟩

theorem normalized_certificate_card_le_degree (p : K[X]) (q : Nat) (hq : q=Fintype.card K)
    (hp : p.Monic) (hdeg : (0 : WithBot Nat)<degree p)
    (s : Finset K) (hs : NormalizedCompleteRootCertificate p q s) :
    s.card ≤ p.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro a ha
  rw [Polynomial.mem_roots hp.ne_zero]
  exact (normalized_certificate_iff p q hq hp hdeg s hs a).2 (Finset.mem_val.mp ha)

#print axioms normalized_certificate_iff
#print axioms normalized_certificate_card_le_degree
#print axioms rootFactor_roots_iff
#print axioms rootFactor_separable
#print axioms normalized_certificate_exists
end AspisR1.FiniteFieldNormalizedRootFactor

import R1FunctionalBatchClean
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Direct joint-list functional binding. The candidate tuple family and all
linear maps/claims are fixed inputs to the two bad sets. This file proves only
the finite polynomial comparison implication; it has no Fiat--Shamir,
source-extraction, uniqueness, or security conclusion. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.JointFunctionalBinding

open Polynomial
open scoped BigOperators

variable {K M T : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup M] [Module K M] [Fintype T] [DecidableEq T]

def batch (gamma : K) (x : Fin 29 → M) : M :=
  ∑ l : Fin 29, gamma ^ l.val • x l

def deltaPolynomial (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K)
    (t : T) (j : Fin 6) : K[X] :=
  ∑ l : Fin 29,
    Polynomial.monomial l.val (F j (tuple t l) - Y j l)

def deltaFamily (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K) :
    T × Fin 6 → K[X] := fun ij => deltaPolynomial tuple F Y ij.1 ij.2

def gammaBad (ts : Finset T) (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K) : Finset K :=
  AspisR1.functionalBadRoots (ts.product (Finset.univ : Finset (Fin 6)))
    (deltaFamily tuple F Y)

def kappaPolynomial (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) (t : T) : K[X] :=
  Polynomial.monomial 0 (F0 (batch gamma (tuple t)) - c0) +
    ∑ j : Fin 6, Polynomial.monomial (j.val + 1)
      ((deltaPolynomial tuple F Y t j).eval gamma)

def kappaBad (ts : Finset T) (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) : Finset K :=
  AspisR1.functionalBadRoots ts
    (kappaPolynomial tuple F F0 Y c0 gamma)

def weightedValue (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (t : T) (gamma kappa : K) : K :=
  F0 (batch gamma (tuple t)) +
    ∑ j : Fin 6, kappa ^ (j.val + 1) * F j (batch gamma (tuple t))

def claimedValue (Y : Fin 6 → Fin 29 → K) (c0 gamma kappa : K) : K :=
  c0 + ∑ j : Fin 6, kappa ^ (j.val + 1) *
    (∑ l : Fin 29, gamma ^ l.val * Y j l)

theorem delta_natDegree_le_28 (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K)
    (t : T) (j : Fin 6) :
    (deltaPolynomial tuple F Y t j).natDegree ≤ 28 := by
  unfold deltaPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l _hl
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem gamma_bad_card_le_16800 (ts : Finset T)
    (tuple : T → Fin 29 → M) (F : Fin 6 → M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (hlist : ts.card ≤ 100) :
    (gammaBad ts tuple F Y).card ≤ 16800 := by
  have hfamily : (ts.product (Finset.univ : Finset (Fin 6))).card ≤ 600 := by
    simp only [Finset.product_eq_sprod, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
    nlinarith [hlist]
  apply AspisR1.functional_bad_roots_card_le_16800 _ _ hfamily
  rintro ⟨t, j⟩ hmem
  exact delta_natDegree_le_28 tuple F Y t j

theorem kappa_natDegree_le_6 (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) (t : T) :
    (kappaPolynomial tuple F F0 Y c0 gamma t).natDegree ≤ 6 := by
  unfold kappaPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _hj
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem kappa_bad_card_le_600 (ts : Finset T)
    (tuple : T → Fin 29 → M) (F : Fin 6 → M →ₗ[K] K)
    (F0 : M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K)
    (c0 gamma : K) (hlist : ts.card ≤ 100) :
    (kappaBad ts tuple F F0 Y c0 gamma).card ≤ 600 := by
  apply AspisR1.functional_bad_roots_card_le_600 ts _ hlist
  intro t _ht
  exact kappa_natDegree_le_6 tuple F F0 Y c0 gamma t

theorem delta_coeff (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K)
    (t : T) (j : Fin 6) (l : Fin 29) :
    (deltaPolynomial tuple F Y t j).coeff l.val =
      F j (tuple t l) - Y j l := by
  unfold deltaPolynomial
  rw [Polynomial.finsetSum_coeff]
  change (Finset.univ.sum (fun b : Fin 29 =>
    (Polynomial.monomial b.val (F j (tuple t b) - Y j b)).coeff l.val)) = _
  rw [Finset.sum_eq_single l]
  · simp [Polynomial.coeff_monomial]
  · intro b hb hne
    have hval : b.val ≠ l.val := by
      intro heq
      exact hne (Fin.ext heq)
    simp [Polynomial.coeff_monomial, hval]
  · simp

theorem delta_eval (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (Y : Fin 6 → Fin 29 → K)
    (t : T) (j : Fin 6) (gamma : K) :
    (deltaPolynomial tuple F Y t j).eval gamma =
      ∑ l : Fin 29, gamma ^ l.val * (F j (tuple t l) - Y j l) := by
  unfold deltaPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro l _hl
  ring

theorem linear_batch (gamma : K) (x : Fin 29 → M)
    (L : M →ₗ[K] K) :
    L (batch gamma x) = ∑ l : Fin 29, gamma ^ l.val * L (x l) := by
  unfold batch
  simp only [map_sum, map_smul, smul_eq_mul]

theorem kappa_eval (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma kappa : K) (t : T) :
    (kappaPolynomial tuple F F0 Y c0 gamma t).eval kappa =
      (F0 (batch gamma (tuple t)) - c0) +
        ∑ j : Fin 6, kappa ^ (j.val + 1) *
          (∑ l : Fin 29, gamma ^ l.val *
            (F j (tuple t l) - Y j l)) := by
  unfold kappaPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_monomial,
    Polynomial.eval_finsetSum]
  simp only [pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rw [delta_eval]
  ring

theorem kappa_eval_eq_weighted_difference (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma kappa : K) (t : T) :
    (kappaPolynomial tuple F F0 Y c0 gamma t).eval kappa =
      weightedValue tuple F F0 t gamma kappa -
        claimedValue Y c0 gamma kappa := by
  rw [kappa_eval]
  unfold weightedValue claimedValue
  have hinner (j : Fin 6) :
      (∑ l : Fin 29, gamma ^ l.val * F j (tuple t l)) -
          (∑ l : Fin 29, gamma ^ l.val * Y j l) =
        ∑ l : Fin 29, gamma ^ l.val *
          (F j (tuple t l) - Y j l) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _hl
    ring
  have houter :
      ∑ j : Fin 6, kappa ^ (j.val + 1) *
          (∑ l : Fin 29, gamma ^ l.val *
            (F j (tuple t l) - Y j l)) =
        (∑ j : Fin 6, kappa ^ (j.val + 1) *
            (∑ l : Fin 29, gamma ^ l.val * F j (tuple t l))) -
          (∑ j : Fin 6, kappa ^ (j.val + 1) *
            (∑ l : Fin 29, gamma ^ l.val * Y j l)) := by
    calc
      ∑ j : Fin 6, kappa ^ (j.val + 1) *
          (∑ l : Fin 29, gamma ^ l.val *
            (F j (tuple t l) - Y j l)) =
        ∑ j : Fin 6, (kappa ^ (j.val + 1) *
          (∑ l : Fin 29, gamma ^ l.val * F j (tuple t l)) -
          kappa ^ (j.val + 1) *
            (∑ l : Fin 29, gamma ^ l.val * Y j l)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [← hinner j]
          ring
      _ = (∑ j : Fin 6, kappa ^ (j.val + 1) *
            (∑ l : Fin 29, gamma ^ l.val * F j (tuple t l))) -
          (∑ j : Fin 6, kappa ^ (j.val + 1) *
            (∑ l : Fin 29, gamma ^ l.val * Y j l)) := by
          rw [Finset.sum_sub_distrib]
  simp_rw [linear_batch gamma (tuple t)]
  rw [houter]
  ring

theorem kappa_coeff_zero (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) (t : T) :
    (kappaPolynomial tuple F F0 Y c0 gamma t).coeff 0 =
      F0 (batch gamma (tuple t)) - c0 := by
  unfold kappaPolynomial
  simp [Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]

theorem kappa_coeff_succ (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) (t : T) (j : Fin 6) :
    (kappaPolynomial tuple F F0 Y c0 gamma t).coeff (j.val + 1) =
      (deltaPolynomial tuple F Y t j).eval gamma := by
  unfold kappaPolynomial
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  have hzero : (Polynomial.monomial 0
      (F0 (batch gamma (tuple t)) - c0)).coeff (j.val + 1) = 0 := by
    simp [Polynomial.coeff_monomial]
  rw [hzero, Finset.sum_eq_single j]
  · simp [Polynomial.coeff_monomial]
  · intro i _hi hne
    by_cases hv : i.val = j.val
    · exact (hne (Fin.ext hv)).elim
    · simp [Polynomial.coeff_monomial, hv]
  · simp

theorem joint_functional_binding
    (ts : Finset T) (tuple : T → Fin 29 → M)
    (F : Fin 6 → M →ₗ[K] K) (F0 : M →ₗ[K] K)
    (Y : Fin 6 → Fin 29 → K) (c0 : K)
    (t : T) (ht : t ∈ ts) (gamma kappa : K)
    (hgamma : gamma ∉ gammaBad ts tuple F Y)
    (hkappa : kappa ∉ kappaBad ts tuple F F0 Y c0 gamma)
    (haccepted : weightedValue tuple F F0 t gamma kappa =
      claimedValue Y c0 gamma kappa) :
    (∀ j : Fin 6, ∀ l : Fin 29, F j (tuple t l) = Y j l) ∧
      F0 (batch gamma (tuple t)) = c0 := by
  have hkapEval : (kappaPolynomial tuple F F0 Y c0 gamma t).eval kappa = 0 := by
    rw [kappa_eval_eq_weighted_difference]
    rw [haccepted]
    simp
  have hkap : kappaPolynomial tuple F F0 Y c0 gamma t = 0 := by
    apply AspisR1.eval_zero_outside_functional_bad_roots ts
      (kappaPolynomial tuple F F0 Y c0 gamma) kappa hkappa t ht hkapEval
  have hdeltaEval (j : Fin 6) :
      (deltaPolynomial tuple F Y t j).eval gamma = 0 := by
    have hc := congrArg (fun p : K[X] => p.coeff (j.val + 1)) hkap
    rw [kappa_coeff_succ] at hc
    exact hc
  have hdelta (j : Fin 6) : deltaPolynomial tuple F Y t j = 0 := by
    have hout : gamma ∉ AspisR1.functionalBadRoots
        (ts.product (Finset.univ : Finset (Fin 6))) (deltaFamily tuple F Y) := by
      simpa [gammaBad] using hgamma
    exact AspisR1.eval_zero_outside_functional_bad_roots
      (ts.product (Finset.univ : Finset (Fin 6))) (deltaFamily tuple F Y)
      gamma hout (t, j) (Finset.mem_product.mpr ⟨ht, Finset.mem_univ j⟩)
      (hdeltaEval j)
  have hF0 : F0 (batch gamma (tuple t)) = c0 := by
    have hc := congrArg (fun p : K[X] => p.coeff 0) hkap
    rw [kappa_coeff_zero] at hc
    exact sub_eq_zero.mp hc
  refine ⟨?_, hF0⟩
  intro j l
  have hc := congrArg (fun p : K[X] => p.coeff l.val) (hdelta j)
  rw [delta_coeff] at hc
  exact sub_eq_zero.mp hc

#print axioms gamma_bad_card_le_16800
#print axioms kappa_bad_card_le_600
#print axioms joint_functional_binding

end AspisR1.JointFunctionalBinding

end

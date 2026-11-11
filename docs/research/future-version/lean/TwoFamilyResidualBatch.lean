import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.Card

/-! Two 22-coordinate residual families batched at ONE subfield challenge
(future-version experiment, stage B).

Purely algebraic. No probability, Fiat--Shamir, commitment-binding, protocol or
source-correspondence claim is made here.

Content: for two residual vectors `r0 r1 : Fin 22 → E` there is a set
`bad2 iota r0 r1` of subfield challenges that
* depends on the two vectors only (not on the challenge),
* has at most 21 elements (not 42), and
* outside which the vanishing of BOTH batched sums forces every coordinate of
  both vectors to be zero.

The first four lemmas restate, for a self-contained module, facts already
proved in `AspisR1.SubfieldBatch` and `AspisR1.ResidualBatch`
(docs/research/100bit-spend-path-20261013/lean); their proofs are the same. -/

set_option autoImplicit false

namespace AspisFuture.TwoFamilyBatch

open Polynomial
open scoped BigOperators

noncomputable section

variable {K E : Type} [Field K] [Field E] [Fintype K]

local instance : DecidableEq K := Classical.decEq K
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A nonzero polynomial over `E` has at most its degree many roots among the
images in `E` of the elements of the finite field `K`. -/
theorem subfield_roots_card_le_natDegree
    (iota : K →+* E) (p : E[X]) (hp : p ≠ 0) :
    (Finset.univ.filter (fun t : K => p.eval (iota t) = 0)).card ≤ p.natDegree := by
  classical
  let bad := Finset.univ.filter (fun t : K => p.eval (iota t) = 0)
  let embedding : K ↪ E := ⟨iota, iota.injective⟩
  have hsubset : bad.map embedding ⊆ p.roots.toFinset := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨t, ht, hty⟩
    subst y
    change iota t ∈ p.roots.toFinset
    rw [Multiset.mem_toFinset, p.mem_roots hp]
    exact (Finset.mem_filter.mp ht).2
  calc
    bad.card = (bad.map embedding).card := by simp
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := p.card_roots'

/-- The 22 residual coordinates as the coefficients of a polynomial. -/
def residualPolynomial (r : Fin 22 → E) : E[X] :=
  ∑ i : Fin 22, Polynomial.monomial i.val (r i)

theorem residualPolynomial_coeff (r : Fin 22 → E) (i : Fin 22) :
    (residualPolynomial r).coeff i.val = r i := by
  classical
  rw [residualPolynomial]
  change (∑ j : Fin 22, Polynomial.monomial j.val (r j)).coeff i.val = r i
  rw [show (∑ j : Fin 22, Polynomial.monomial j.val (r j)).coeff i.val =
      ∑ j : Fin 22, (Polynomial.monomial j.val (r j)).coeff i.val by
        exact map_sum (Polynomial.lcoeff E i.val)
          (fun j : Fin 22 => Polynomial.monomial j.val (r j)) Finset.univ]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    have hne : j.val ≠ i.val := by
      intro hv
      exact hji (Fin.ext hv)
    simp [Polynomial.coeff_monomial, hne]
  · simp

theorem residualPolynomial_eq_zero_iff (r : Fin 22 → E) :
    residualPolynomial r = 0 ↔ ∀ i, r i = 0 := by
  constructor
  · intro h i
    have hcoeff := congrArg (fun p : E[X] => p.coeff i.val) h
    simpa only [residualPolynomial_coeff, Polynomial.coeff_zero] using hcoeff
  · intro hr
    classical
    simp [residualPolynomial, hr]

theorem residualPolynomial_natDegree_le (r : Fin 22 → E) :
    (residualPolynomial r).natDegree ≤ 21 := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [residualPolynomial]
  rw [show (∑ i : Fin 22, Polynomial.monomial i.val (r i)).coeff m =
      ∑ i : Fin 22, (Polynomial.monomial i.val (r i)).coeff m by
        exact map_sum (Polynomial.lcoeff E m)
          (fun i : Fin 22 => Polynomial.monomial i.val (r i)) Finset.univ]
  apply Finset.sum_eq_zero
  intro i _hi
  have hne : m ≠ i.val := by omega
  simp [Polynomial.coeff_monomial, Ne.symm hne]

omit [Fintype K] in
theorem eval_residualPolynomial (iota : K →+* E) (rho : K)
    (r : Fin 22 → E) :
    (residualPolynomial r).eval (iota rho) =
      ∑ i : Fin 22, (iota rho) ^ i.val * r i := by
  classical
  simp [residualPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, mul_comm]

/-- The subfield roots of the residual polynomial of one family. -/
def rootsIn (iota : K →+* E) (r : Fin 22 → E) : Finset K :=
  Finset.univ.filter fun rho : K => (residualPolynomial r).eval (iota rho) = 0

/-- Bad challenges for the PAIR: the subfield roots of the first family whose
residual polynomial is nonzero, and no challenge when both vanish. The choice
is made from the two vectors alone. -/
def bad2 (iota : K →+* E) (r0 r1 : Fin 22 → E) : Finset K :=
  if residualPolynomial r0 ≠ 0 then rootsIn iota r0
    else if residualPolynomial r1 ≠ 0 then rootsIn iota r1
    else ∅

/-- The pair has at most 21 bad challenges: batching a second family at the
same challenge does not double the cap. -/
theorem bad2_card_le_21 (iota : K →+* E) (r0 r1 : Fin 22 → E) :
    (bad2 iota r0 r1).card ≤ 21 := by
  have one : ∀ r : Fin 22 → E, residualPolynomial r ≠ 0 → (rootsIn iota r).card ≤ 21 := by
    intro r hr
    exact (subfield_roots_card_le_natDegree iota (residualPolynomial r) hr).trans
      (residualPolynomial_natDegree_le r)
  unfold bad2
  by_cases h0 : residualPolynomial r0 ≠ 0
  · rw [if_pos h0]
    exact one r0 h0
  · rw [if_neg h0]
    by_cases h1 : residualPolynomial r1 ≠ 0
    · rw [if_pos h1]
      exact one r1 h1
    · rw [if_neg h1]
      simp

/-- Outside the bad set, the two batched equalities imply all 44 coordinate
equalities. This is the statement the batched first-fold check needs in place
of the 22 per-query equalities of the pinned verifier. -/
theorem all_zero_of_both_evals_zero_outside_bad2 (iota : K →+* E) (rho : K)
    (r0 r1 : Fin 22 → E)
    (hrho : rho ∉ bad2 iota r0 r1)
    (h0 : ∑ i : Fin 22, (iota rho) ^ i.val * r0 i = 0)
    (h1 : ∑ i : Fin 22, (iota rho) ^ i.val * r1 i = 0) :
    (∀ i, r0 i = 0) ∧ (∀ i, r1 i = 0) := by
  have root : ∀ r : Fin 22 → E, (∑ i : Fin 22, (iota rho) ^ i.val * r i = 0) →
      rho ∈ rootsIn iota r := by
    intro r hr
    unfold rootsIn
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ rho, by rw [eval_residualPolynomial]; exact hr⟩
  by_cases hp0 : residualPolynomial r0 ≠ 0
  · exact False.elim (hrho (by unfold bad2; rw [if_pos hp0]; exact root r0 h0))
  · have z0 : residualPolynomial r0 = 0 := not_not.mp hp0
    by_cases hp1 : residualPolynomial r1 ≠ 0
    · exact False.elim (hrho (by unfold bad2; rw [if_neg hp0, if_pos hp1]; exact root r1 h1))
    · have z1 : residualPolynomial r1 = 0 := not_not.mp hp1
      exact ⟨(residualPolynomial_eq_zero_iff r0).mp z0, (residualPolynomial_eq_zero_iff r1).mp z1⟩

#print axioms bad2_card_le_21
#print axioms all_zero_of_both_evals_zero_outside_bad2

end

end AspisFuture.TwoFamilyBatch

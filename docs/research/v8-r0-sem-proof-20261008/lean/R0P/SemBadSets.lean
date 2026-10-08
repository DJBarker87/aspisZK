import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! G10: deterministic cardinality and polynomial lemmas for the fixed
`SemLedger.lean` design at 1074cbc49. The coordinate-union theorem uses
only the stated per-coordinate cardinality bounds; its polynomial
specialization assumes nonzero round differences, as in the ledger.
Both tuple-counting results include n = 0.

The multilinear bound uses `MvPolynomial.schwartz_zippel_sum_degreeOf`,
Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean:179–185, from cached
Mathlib revision 81a5d257c8e410db227a6665ed08f64fea08e997.
Product injectivity uses `Polynomial.roots_multiset_prod_X_sub_C` over
the integral domain K[X]; the coefficient-degree proof is a symbolic
multiset induction. No probability or adaptive-strategy claim is made. -/

set_option autoImplicit false

noncomputable section

namespace R0P.SemBadSets

open Polynomial

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A nonzero univariate polynomial has at most its degree many bad field
values. -/
theorem univariate_bad_card [Fintype K] (p : K[X]) (hp : p ≠ 0)
    (d : Nat) (hd : p.natDegree ≤ d) :
    (Finset.univ.filter (fun x : K => p.eval x = 0)).card ≤ d := by
  classical
  have hsub : (Finset.univ.filter (fun x : K => p.eval x = 0)) ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset, p.mem_roots hp]
    exact hx.2
  calc
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := p.card_roots'
    _ ≤ d := hd

#print axioms univariate_bad_card

omit [Field K] in
private theorem coordinate_bad_card [Fintype K] {n : Nat} (bad : Finset K)
    (i : Fin n) :
    (Finset.univ.filter (fun α : Fin n → K => α i ∈ bad)).card =
      bad.card * Fintype.card K ^ (n - 1) := by
  classical
  have hfiber (x : K) :
      (Finset.univ.filter (fun α : Fin n → K => α i = x)).card =
        Fintype.card K ^ (n - 1) := by
    simpa using Fintype.card_filter_piFinset_const_eq_of_mem
      (Finset.univ : Finset K) i (Finset.mem_univ x)
  calc
    _ = ∑ x ∈ bad, (Finset.univ.filter (fun α : Fin n → K => α i = x)).card :=
      (Finset.sum_card_fiberwise_eq_card_filter Finset.univ bad (fun α : Fin n → K => α i)).symm
    _ = ∑ x ∈ bad, Fintype.card K ^ (n - 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hfiber x
    _ = bad.card * Fintype.card K ^ (n - 1) := by simp

#print axioms coordinate_bad_card

omit [Field K] in
/-- A union of coordinate bad cylinders has the elementary union bound, for
arbitrary coordinate bad sets. -/
theorem round_bad_union_card [Fintype K] {n d : Nat}
    (bad : Fin n → Finset K) (hbad : ∀ i, (bad i).card ≤ d) :
    Fintype.card {α : Fin n → K // ∃ i, α i ∈ bad i} ≤
      n * d * Fintype.card K ^ (n - 1) := by
  classical
  let cyl : Fin n → Finset (Fin n → K) :=
    fun i => Finset.univ.filter (fun α => α i ∈ bad i)
  have hevent : Finset.univ.filter (fun α : Fin n → K => ∃ i, α i ∈ bad i) =
      Finset.univ.biUnion cyl := by
    ext α
    simp [cyl]
  calc
    _ = (Finset.univ.filter (fun α : Fin n → K => ∃ i, α i ∈ bad i)).card := by
      simp [Fintype.card_subtype]
    _ = (Finset.univ.biUnion cyl).card := by rw [hevent]
    _ ≤ ∑ i ∈ Finset.univ, (cyl i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.univ, d * Fintype.card K ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      change (Finset.univ.filter (fun α : Fin n → K => α i ∈ bad i)).card ≤ _
      rw [coordinate_bad_card]
      exact Nat.mul_le_mul_right _ (hbad i)
    _ = n * d * Fintype.card K ^ (n - 1) := by
      simp [Nat.mul_assoc]

#print axioms round_bad_union_card

/-- The sumcheck-round bad tuples are contained in the union of the roots of
the round polynomials, each lifted along its coordinate cylinder. -/
theorem sumcheck_rounds_bad [Fintype K] {n d : Nat}
    (p : Fin n → K[X]) (hnz : ∀ i, p i ≠ 0)
    (hdeg : ∀ i, (p i).natDegree ≤ d) :
    Fintype.card {α : Fin n → K // ∃ i, (p i).eval (α i) = 0} ≤
      n * d * Fintype.card K ^ (n - 1) := by
  classical
  let bad : Fin n → Finset K := fun i => Finset.univ.filter (fun x => (p i).eval x = 0)
  have hb : ∀ i, (bad i).card ≤ d := by
    intro i
    exact univariate_bad_card (p i) (hnz i) d (hdeg i)
  simpa [bad] using round_bad_union_card bad hb

#print axioms sumcheck_rounds_bad

/-- The Schwartz-Zippel zero set bound for a polynomial of individual degree
at most one. -/
theorem zerocheck_bad [Fintype K] {n : Nat} (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (hdeg : ∀ i, p.degreeOf i ≤ 1) :
    Fintype.card {z : Fin n → K // MvPolynomial.eval z p = 0} ≤
      n * Fintype.card K ^ (n - 1) := by
  classical
  let N := Fintype.card {z : Fin n → K // MvPolynomial.eval z p = 0}
  let q : ℚ≥0 := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : K)⟩
  have hsz := MvPolynomial.schwartz_zippel_sum_degreeOf (R := K) hp
    (fun _ : Fin n => (Finset.univ : Finset K))
  have hsz' : (N : ℚ≥0) / q ^ n ≤
      ∑ i : Fin n, ((p.degreeOf i : ℚ≥0) / q) := by
    simpa [N, q, Fintype.card_subtype, Fintype.card_piFinset_const] using hsz
  have hdeg' : ∑ i : Fin n, ((p.degreeOf i : ℚ≥0) / q) ≤ (n : ℚ≥0) / q := by
    calc
      _ ≤ ∑ _i : Fin n, ((1 : ℚ≥0) / q) := by
        apply Finset.sum_le_sum
        intro i hi
        exact div_le_div_of_nonneg_right (by exact_mod_cast hdeg i) (by positivity)
      _ = (n : ℚ≥0) / q := by simp [div_eq_mul_inv]
  have hmul : (N : ℚ≥0) ≤ ((n : ℚ≥0) / q) * q ^ n :=
    (div_le_iff₀ (pow_pos hq n)).mp (hsz'.trans hdeg')
  have hpow : ((n : ℚ≥0) / q) * q ^ n =
      (n : ℚ≥0) * q ^ (n - 1) := by
    by_cases hn : n = 0
    · simp [hn]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp only [Nat.succ_sub_one]
      rw [pow_succ]
      field_simp [ne_of_gt hq]
  have hnat : N ≤ n * Fintype.card K ^ (n - 1) := by
    have hR := hmul.trans_eq hpow
    change (N : ℚ≥0) ≤ (n : ℚ≥0) * (Fintype.card K : ℚ≥0) ^ (n - 1) at hR
    exact_mod_cast hR
  simpa [N] using hnat

#print axioms zerocheck_bad

private def rootProduct (S : Multiset (K[X])) : (K[X])[X] :=
  (S.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod

#print axioms rootProduct

private theorem rootProduct_coeff_degree (S : Multiset (K[X]))
    (hS : ∀ q ∈ S, q.natDegree ≤ 16) (j : Nat) :
    ((rootProduct S).coeff j).natDegree ≤ 16 * S.card := by
  classical
  induction S using Multiset.induction_on generalizing j with
  | empty =>
      by_cases hj : j = 0
      · subst j
        simp [rootProduct]
      · simp [rootProduct, Polynomial.coeff_one, hj]
  | cons q S ih =>
      have hq : q.natDegree ≤ 16 := hS q (by simp)
      have hS' : ∀ x ∈ S, x.natDegree ≤ 16 := by
        intro x hx
        exact hS x (by simp [hx])
      by_cases hj : j = 0
      · subst j
        have hb := ih hS' 0
        simp only [rootProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        change ((((Polynomial.X : Polynomial (K[X])) - Polynomial.C q) *
          rootProduct S).coeff 0).natDegree ≤ 16 * (S.card + 1)
        rw [Polynomial.mul_coeff_zero]
        have hcoeff0 : ((Polynomial.X : Polynomial (K[X])) - Polynomial.C q).coeff 0 = -q := by
          simp
        rw [hcoeff0]
        calc
          _ ≤ (-q).natDegree + ((rootProduct S).coeff 0).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 16 + 16 * S.card := Nat.add_le_add (by simpa using hq) hb
          _ = 16 * (S.card + 1) := by omega
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hb := ih hS' k
        have hb' := ih hS' (k + 1)
        simp only [rootProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        change ((((Polynomial.X : Polynomial (K[X])) - Polynomial.C q) *
          rootProduct S).coeff (k + 1)).natDegree ≤ 16 * (S.card + 1)
        rw [Polynomial.coeff_X_sub_C_mul]
        have hmul : (q * (rootProduct S).coeff (k + 1)).natDegree ≤ 16 + 16 * S.card := by
          calc
            _ ≤ q.natDegree + ((rootProduct S).coeff (k + 1)).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 16 + 16 * S.card := Nat.add_le_add hq hb'
        calc
          _ ≤ max ((rootProduct S).coeff k).natDegree
              (q * (rootProduct S).coeff (k + 1)).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ 16 * (S.card + 1) := by omega

#print axioms rootProduct_coeff_degree

/-- Distinct root multisets give distinct monic products. Moreover every
coefficient of their difference has λ-degree at most sixteen times the larger
multiset size, so a nonzero coefficient exists within that bound. -/
theorem product_difference_coeff (S T : Multiset (K[X])) (hne : S ≠ T)
    (hS : ∀ q ∈ S, q.natDegree ≤ 16) (hT : ∀ q ∈ T, q.natDegree ≤ 16) :
    (S.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod ≠
      (T.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod ∧
    ∃ j, (((S.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod -
      (T.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod).coeff j) ≠ 0 ∧
      ((((S.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod -
        (T.map (fun q => (Polynomial.X : Polynomial (K[X])) - Polynomial.C q)).prod).coeff j).natDegree ≤
          16 * max S.card T.card) := by
  classical
  change rootProduct S ≠ rootProduct T ∧
    ∃ j, (rootProduct S - rootProduct T).coeff j ≠ 0 ∧
      ((rootProduct S - rootProduct T).coeff j).natDegree ≤ 16 * max S.card T.card
  have hneProd : rootProduct S ≠ rootProduct T := by
    intro heq
    have hroots := congrArg Polynomial.roots heq
    simp [rootProduct, Polynomial.roots_multiset_prod_X_sub_C] at hroots
    exact hne hroots
  have hdiff : rootProduct S - rootProduct T ≠ 0 := sub_ne_zero.mpr hneProd
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hdiff
  have hj' : (rootProduct S - rootProduct T).coeff j ≠ 0 := by
    simpa only [Polynomial.mem_support_iff] using hj
  refine ⟨hneProd, j, hj', ?_⟩
  calc
    _ ≤ max ((rootProduct S).coeff j).natDegree ((rootProduct T).coeff j).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ max (16 * S.card) (16 * T.card) :=
      max_le_max (rootProduct_coeff_degree S hS j) (rootProduct_coeff_degree T hT j)
    _ ≤ 16 * max S.card T.card := by
      calc
        _ ≤ max (16 * max S.card T.card) (16 * max S.card T.card) := max_le_max
          (Nat.mul_le_mul_left 16 (Nat.le_max_left S.card T.card))
          (Nat.mul_le_mul_left 16 (Nat.le_max_right S.card T.card))
        _ = 16 * max S.card T.card := max_self _

#print axioms product_difference_coeff

end R0P.SemBadSets

end

-- Coordinator audit of the generic public signatures and their premises.
#check @R0P.SemBadSets.univariate_bad_card
#check @R0P.SemBadSets.round_bad_union_card
#check @R0P.SemBadSets.sumcheck_rounds_bad
#check @R0P.SemBadSets.zerocheck_bad
#check @R0P.SemBadSets.product_difference_coeff

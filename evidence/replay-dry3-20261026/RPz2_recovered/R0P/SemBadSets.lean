import R0P.Zerocheck
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
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

/-! Continuation G10: fixed function-level composition from Sumcheck.lean and
Zerocheck.lean at a22519dc8. The recursive MLE bound below uses the leading
coordinate and affine-root uniqueness; it does not invoke the earlier
MvPolynomial bound. The adaptive count preserves each strategy prefix in a
strengthening of the recursive soundness argument, because the existential
statement of Sumcheck.sound alone does not retain that dependency.

The explicit prefix embedding uses Fin.castLE i.isLt.le, correcting the
brief's ill-typed j.isLt.le with the user's approval. No event, degree bound,
or acceptance premise was changed. All finite counts remain symbolic. -/

set_option autoImplicit false

noncomputable section

namespace R0P.SemBadSets

open Polynomial
open R0P.Sumcheck

variable {K : Type} [Field K]

/-- Individual functional degree, retaining the bound after every leading
restriction and supplying a polynomial on every leading-coordinate line. -/
def MLDeg (d : Nat) : (n : Nat) → ((Fin n → K) → K) → Prop
  | 0, _ => True
  | n+1, G => (∀ x, MLDeg d n (fun v => G (Fin.cons x v))) ∧
      ∀ v : Fin n → K, ∃ p : K[X], p.natDegree ≤ d ∧
        ∀ x, p.eval x = G (Fin.cons x v)

#print axioms MLDeg

theorem mlDeg_const (d n : Nat) (c : K) : MLDeg d n (fun _ => c) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun _ => ih, fun _ => ⟨C c, ?_, ?_⟩⟩
      · simpa only [natDegree_C] using Nat.zero_le d
      · intro x
        exact eval_C

#print axioms mlDeg_const

theorem mlDeg_mono {d e n : Nat} {G : (Fin n → K) → K}
    (h : MLDeg d n G) (hde : d ≤ e) : MLDeg e n G := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (h.1 x), ?_⟩
      intro v
      obtain ⟨p, hp, he⟩ := h.2 v
      exact ⟨p, hp.trans hde, he⟩

#print axioms mlDeg_mono

theorem mlDeg_add {d e n : Nat} {G H : (Fin n → K) → K}
    (hG : MLDeg d n G) (hH : MLDeg e n H) :
    MLDeg (max d e) n (fun v => G v + H v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (hG.1 x) (hH.1 x), ?_⟩
      intro v
      obtain ⟨p, hp, hpe⟩ := hG.2 v
      obtain ⟨q, hq, hqe⟩ := hH.2 v
      refine ⟨p + q, (natDegree_add_le p q).trans (max_le_max hp hq), ?_⟩
      intro x
      rw [eval_add, hpe, hqe]

#print axioms mlDeg_add

theorem mlDeg_mul {d e n : Nat} {G H : (Fin n → K) → K}
    (hG : MLDeg d n G) (hH : MLDeg e n H) :
    MLDeg (d + e) n (fun v => G v * H v) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨fun x => ih (hG.1 x) (hH.1 x), ?_⟩
      intro v
      obtain ⟨p, hp, hpe⟩ := hG.2 v
      obtain ⟨q, hq, hqe⟩ := hH.2 v
      refine ⟨p * q, natDegree_mul_le.trans (Nat.add_le_add hp hq), ?_⟩
      intro x
      rw [eval_mul, hpe, hqe]

#print axioms mlDeg_mul

theorem mlDeg_smul {d n : Nat} {G : (Fin n → K) → K}
    (c : K) (hG : MLDeg d n G) : MLDeg d n (fun v => c * G v) := by
  simpa only [Nat.zero_add] using mlDeg_mul (mlDeg_const 0 n c) hG

#print axioms mlDeg_smul

theorem mlDeg_sum {ι : Type} (s : Finset ι) {d n : Nat}
    (G : ι → (Fin n → K) → K) (hG : ∀ i ∈ s, MLDeg d n (G i)) :
    MLDeg d n (fun v => ∑ i ∈ s, G i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using mlDeg_const d n (0 : K)
  | @insert i s his ih =>
      have hi := hG i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert his, max_self] using mlDeg_add hi hs

#print axioms mlDeg_sum

/-- Summing degree-bounded polynomial functions on Boolean tails preserves
the bound. This is a symbolic recursion on the dimension, not enumeration. -/
private theorem bsum_polynomial {d : Nat} (n : Nat)
    (H : (Fin n → K) → K → K)
    (hH : ∀ v, ∃ p : K[X], p.natDegree ≤ d ∧ ∀ x, p.eval x = H v x) :
    ∃ p : K[X], p.natDegree ≤ d ∧ ∀ x, p.eval x = bsum n (fun v => H v x) := by
  induction n with
  | zero => exact hH (fun i => i.elim0)
  | succ n ih =>
      obtain ⟨p, hp, hpe⟩ := ih (fun v => H (Fin.cons 0 v))
        (fun v => hH (Fin.cons 0 v))
      obtain ⟨q, hq, hqe⟩ := ih (fun v => H (Fin.cons 1 v))
        (fun v => hH (Fin.cons 1 v))
      refine ⟨p + q, (natDegree_add_le p q).trans (max_le hp hq), ?_⟩
      intro x
      rw [eval_add, hpe, hqe]
      rfl

#print axioms bsum_polynomial

theorem mlDeg_indDeg {d n : Nat} {G : (Fin n → K) → K}
    (hG : MLDeg d n G) : IndDeg d n G := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨?_, fun x => ih (hG.1 x)⟩
      exact bsum_polynomial n (fun v x => G (Fin.cons x v)) hG.2

#print axioms mlDeg_indDeg

theorem indDeg_of_multilinear_product {d e n : Nat} {G H : (Fin n → K) → K}
    (hG : MLDeg d n G) (hH : MLDeg e n H) :
    IndDeg (d + e) n (fun v => G v * H v) :=
  mlDeg_indDeg (mlDeg_mul hG hH)

#print axioms indDeg_of_multilinear_product

private theorem affine_polynomial (a b : K) :
    ∃ p : K[X], p.natDegree ≤ 1 ∧ ∀ x, p.eval x = (1-x)*a+x*b := by
  refine ⟨(1-X)*C a + X*C b, ?_, ?_⟩
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      simpa only [natDegree_C, Nat.add_zero] using
        (natDegree_sub_le (1 : K[X]) X).trans (by simp)
    · apply natDegree_mul_le.trans
      simp only [natDegree_X, natDegree_C, Nat.add_zero, le_refl]
  · intro x
    simp only [eval_add, eval_mul, eval_sub, eval_one, eval_X, eval_C]

#print axioms affine_polynomial

theorem mlDeg_eqwB (n : Nat) (b : Fin n → Bool) :
    MLDeg 1 n (fun z : Fin n → K => eqwB n z b) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      constructor
      · intro x
        simpa only [eqwB, Fin.cons_zero, Fin.tail_cons] using
          mlDeg_smul (if b 0 then x else 1-x) (ih (Fin.tail b))
      · intro v
        cases hb : b 0 with
        | false =>
            obtain ⟨p, hp, he⟩ := affine_polynomial (eqwB n v (Fin.tail b)) 0
            refine ⟨p, hp, ?_⟩
            intro x
            simpa only [eqwB, Fin.cons_zero, Fin.tail_cons, hb, Bool.false_eq_true,
              ↓reduceIte, mul_zero, add_zero] using he x
        | true =>
            obtain ⟨p, hp, he⟩ := affine_polynomial 0 (eqwB n v (Fin.tail b))
            refine ⟨p, hp, ?_⟩
            intro x
            simpa only [eqwB, Fin.cons_zero, Fin.tail_cons, hb, ↓reduceIte,
              mul_zero, zero_add] using he x

#print axioms mlDeg_eqwB

theorem mlDeg_mle (n : Nat) (f : (Fin n → Bool) → K) :
    MLDeg 1 n (mle n f) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      constructor
      · intro x
        simpa only [mle, Fin.cons_zero, Fin.tail_cons, max_self] using
          mlDeg_add
            (mlDeg_smul (1-x) (ih (fun b => f (Fin.cons false b))))
            (mlDeg_smul x (ih (fun b => f (Fin.cons true b))))
      · intro v
        simpa only [mle, Fin.cons_zero, Fin.tail_cons] using
          affine_polynomial (mle n (fun b => f (Fin.cons false b)) v)
            (mle n (fun b => f (Fin.cons true b)) v)

#print axioms mlDeg_mle

end R0P.SemBadSets

end

set_option autoImplicit false

namespace R0P.SemBadSets

open Classical in
/-- Count a predicate on finite vectors by its leading-coordinate fibers.
The equivalence is symbolic for arbitrary dimension and finite type. -/
theorem filter_card_fin_cons {K : Type} [Fintype K] [DecidableEq K]
    (n : Nat) (P : (Fin (n+1) → K) → Prop) :
    (Finset.univ.filter P).card =
      ∑ x : K, (Finset.univ.filter (fun y : Fin n → K => P (Fin.cons x y))).card := by
  classical
  let e : {z : Fin (n+1) → K // P z} ≃
      Σ x : K, {y : Fin n → K // P (Fin.cons x y)} :=
    { toFun := fun z => ⟨z.1 0, ⟨Fin.tail z.1, by
        simpa only [Fin.cons_self_tail] using z.2⟩⟩
      invFun := fun z => ⟨Fin.cons z.1 z.2.1, z.2.2⟩
      left_inv := fun z => Subtype.ext (Fin.cons_self_tail z.1)
      right_inv := by
        rintro ⟨x, y, hy⟩
        rfl }
  calc
    _ = Fintype.card {z : Fin (n+1) → K // P z} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (Σ x : K, {y : Fin n → K // P (Fin.cons x y)}) :=
      Fintype.card_congr e
    _ = ∑ x : K, Fintype.card {y : Fin n → K // P (Fin.cons x y)} :=
      Fintype.card_sigma
    _ = _ := by simp only [Fintype.card_subtype]

#print axioms filter_card_fin_cons

end R0P.SemBadSets

set_option autoImplicit false

namespace R0P.SemBadSets

open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable section

local instance : DecidableEq K := Classical.decEq K
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private def muRootPoly (a s1 s2 : K) : K[X] :=
  C a + (C s1 * X + C s2 * X ^ 2)

#print axioms muRootPoly

private theorem badMu_card_of_nonzero (a s1 s2 : K)
    (hcoeff : a ≠ 0 ∨ s1 ≠ 0 ∨ s2 ≠ 0) :
    (Finset.univ.filter (fun μ : K => R0P.Sumcheck.BadMu a s1 s2 μ)).card ≤ 2 := by
  classical
  let p := muRootPoly a s1 s2
  have hp : p ≠ 0 := by
    intro h
    have h0 : p.coeff 0 = 0 := by rw [h]; simp
    have h1 : p.coeff 1 = 0 := by rw [h]; simp
    have h2 : p.coeff 2 = 0 := by rw [h]; simp
    have ha : a = 0 := by simpa [p, muRootPoly] using h0
    have hs1 : s1 = 0 := by simpa [p, muRootPoly] using h1
    have hs2 : s2 = 0 := by simpa [p, muRootPoly] using h2
    rcases hcoeff with ha' | hs1' | hs2'
    · exact ha' ha
    · exact hs1' hs1
    · exact hs2' hs2
  have hdeg : p.natDegree ≤ 2 := by
    dsimp [p, muRootPoly]
    calc
      _ ≤ max ((C a).natDegree) ((C s1 * X + C s2 * X ^ 2).natDegree) :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 2 := by
        apply max_le
        · simp
        · calc
            _ ≤ max (C s1 * X).natDegree (C s2 * X ^ 2).natDegree :=
              Polynomial.natDegree_add_le _ _
            _ ≤ 2 := max_le
              (calc
                _ ≤ (C s1).natDegree + X.natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + 1 := Nat.add_le_add (by simp) (by simp)
                _ ≤ 2 := by omega)
              (calc
                _ ≤ (C s2).natDegree + (X ^ 2).natDegree := Polynomial.natDegree_mul_le
                _ ≤ 0 + 2 := Nat.add_le_add (by simp) (by simp)
                _ ≤ 2 := by omega)
  have heval (μ : K) : p.eval μ = a + μ * s1 + μ ^ 2 * s2 := by
    simp [p, muRootPoly]
    ring_nf
  have hsub : (Finset.univ.filter (fun μ : K => R0P.Sumcheck.BadMu a s1 s2 μ)) ⊆
      Finset.univ.filter (fun μ : K => p.eval μ = 0) := by
    intro μ hμ
    rw [Finset.mem_filter] at hμ ⊢
    rcases hμ.2 with ⟨_, hzero⟩
    exact ⟨hμ.1, by rw [heval]; exact hzero⟩
  calc
    _ ≤ (Finset.univ.filter (fun μ : K => p.eval μ = 0)).card := Finset.card_le_card hsub
    _ ≤ 2 := by
      have huni := univariate_bad_card p hp 2 hdeg
      convert huni using 1
      congr 1
      ext μ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

#print axioms badMu_card_of_nonzero

theorem badMu_card (a s1 s2 : K) :
    (Finset.univ.filter (fun μ : K => R0P.Sumcheck.BadMu a s1 s2 μ)).card ≤ 2 := by
  classical
  by_cases hcoeff : a ≠ 0 ∨ s1 ≠ 0 ∨ s2 ≠ 0
  · exact badMu_card_of_nonzero a s1 s2 hcoeff
  · have hempty : (Finset.univ.filter
        (fun μ : K => R0P.Sumcheck.BadMu a s1 s2 μ)) = ∅ := by
      ext μ
      simp [R0P.Sumcheck.BadMu, hcoeff]
    rw [hempty]
    simp

#print axioms badMu_card

private def thetaRootPoly (lanes : Fin 29 → (Fin 10 → Bool) → K)
    (b : Fin 10 → Bool) : K[X] :=
  ∑ i : Fin 29, C (lanes i b) * X ^ i.val

#print axioms thetaRootPoly

private theorem badTheta_card_of_nonzero (lanes : Fin 29 → (Fin 10 → Bool) → K)
    (hnz : ∃ i b, lanes i b ≠ 0) :
    (Finset.univ.filter (fun θ : K => R0P.Sumcheck.BadTheta lanes θ)).card ≤ 28 := by
  classical
  obtain ⟨i₀, b₀, hi₀⟩ := hnz
  let p := thetaRootPoly lanes b₀
  have hcoeff : p.coeff i₀.val = lanes i₀ b₀ := by
    simp only [p, thetaRootPoly, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j hj hji
      have hval : j.val ≠ i₀.val := fun h => hji (Fin.ext h)
      simp [Ne.symm hval]
    · simp
  have hp : p ≠ 0 := by
    intro h
    have hzero : p.coeff i₀.val = 0 := by rw [h]; simp
    have : lanes i₀ b₀ = 0 := hcoeff ▸ hzero
    exact hi₀ this
  have hdeg : p.natDegree ≤ 28 := by
    dsimp [p, thetaRootPoly]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    calc
      _ ≤ (C (lanes i b₀)).natDegree + (X ^ i.val).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + i.val := Nat.add_le_add (by simp) (by simp)
      _ ≤ 28 := by omega
  have heval (θ : K) : p.eval θ = R0P.Sumcheck.lanesComp θ lanes b₀ := by
    simp only [p, thetaRootPoly, eval_finsetSum, eval_mul,
      eval_C, eval_pow, eval_X]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_comm]
  have hsub : (Finset.univ.filter (fun θ : K => R0P.Sumcheck.BadTheta lanes θ)) ⊆
      Finset.univ.filter (fun θ : K => p.eval θ = 0) := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ ⊢
    have hzero := hθ.2.2 b₀
    exact ⟨hθ.1, by rw [heval]; exact hzero⟩
  calc
    _ ≤ (Finset.univ.filter (fun θ : K => p.eval θ = 0)).card := Finset.card_le_card hsub
    _ ≤ 28 := by
      have huni := univariate_bad_card p hp 28 hdeg
      convert huni using 1
      congr 1
      ext θ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

#print axioms badTheta_card_of_nonzero

theorem badTheta_card (lanes : Fin 29 → (Fin 10 → Bool) → K) :
    (Finset.univ.filter (fun θ : K => R0P.Sumcheck.BadTheta lanes θ)).card ≤ 28 := by
  classical
  by_cases hnz : ∃ i b, lanes i b ≠ 0
  · exact badTheta_card_of_nonzero lanes hnz
  · have hempty : (Finset.univ.filter
        (fun θ : K => R0P.Sumcheck.BadTheta lanes θ)) = ∅ := by
      ext θ
      simp [R0P.Sumcheck.BadTheta, hnz]
    rw [hempty]
    simp

#print axioms badTheta_card

omit [Fintype K] [DecidableEq K] in
private theorem affine_zero_unique (a b x y : K)
    (hx : a + x * (b - a) = 0) (hy : a + y * (b - a) = 0)
    (hab : a ≠ 0 ∨ b ≠ 0) : x = y := by
  have hprod : (x - y) * (b - a) = 0 := by
    calc
      _ = (a + x * (b - a)) - (a + y * (b - a)) := by ring
      _ = 0 := by rw [hx, hy]; ring
  rcases mul_eq_zero.mp hprod with hxy | hba
  · exact sub_eq_zero.mp hxy
  · have ha : a = 0 := by simpa [hba] using hx
    have hba' : b = a := sub_eq_zero.mp hba
    subst b
    rcases hab with h | h <;> contradiction

#print axioms affine_zero_unique

/-- A nonzero function on the Boolean cube has at most `n |K|^(n-1)` zeros
under its recursive multilinear extension. The successor proof counts the
first-coordinate fibers after the symbolic `Fin.cons` split. -/
private theorem mle_bad_card_of_witness : ∀ (n : Nat) (f : (Fin n → Bool) → K),
    (∃ b, f b ≠ 0) →
      (Finset.univ.filter (fun z : Fin n → K => R0P.Sumcheck.mle n f z = 0)).card ≤
        n * Fintype.card K ^ (n - 1)
  | 0, f, hf => by
      classical
      have hval : f (fun i : Fin 0 => i.elim0) ≠ 0 := by
        obtain ⟨b, hb⟩ := hf
        have hb' : b = fun i : Fin 0 => i.elim0 := by
          funext i
          exact i.elim0
        simpa [hb'] using hb
      have hempty : (Finset.univ.filter
          (fun z : Fin 0 → K => R0P.Sumcheck.mle 0 f z = 0)) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
        constructor
        · intro hz
          exact hval (by simpa [R0P.Sumcheck.mle] using hz)
        · intro hz
          exact False.elim hz
      rw [hempty]
      simp
  | n + 1, f, hf => by
      classical
      obtain ⟨b, hb⟩ := hf
      let f0 : (Fin n → Bool) → K := fun v => f (Fin.cons false v)
      let f1 : (Fin n → Bool) → K := fun v => f (Fin.cons true v)
      let A : (Fin n → K) → K := R0P.Sumcheck.mle n f0
      let B : (Fin n → K) → K := R0P.Sumcheck.mle n f1
      let g : (Fin n → Bool) → K := if b 0 then f1 else f0
      have hbcons : b = Fin.cons (b 0) (Fin.tail b) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      have hg : ∃ v, g v ≠ 0 := by
        refine ⟨Fin.tail b, ?_⟩
        have hb' : f (Fin.cons (b 0) (Fin.tail b)) ≠ 0 := by
          rw [← hbcons]
          exact hb
        by_cases hbit : b 0
        · simpa [g, f1, hbit] using hb'
        · simpa [g, f0, hbit] using hb'
      have htail := mle_bad_card_of_witness n g hg
      let Both : Finset (Fin n → K) := Finset.univ.filter
        (fun v => A v = 0 ∧ B v = 0)
      let Gzero : Finset (Fin n → K) := Finset.univ.filter (fun v => R0P.Sumcheck.mle n g v = 0)
      let Z : Finset (Fin (n + 1) → K) := Finset.univ.filter
        (fun z => R0P.Sumcheck.mle (n + 1) f z = 0)
      let R0 : Finset (Fin (n + 1) → K) := Finset.univ.filter
        (fun z => A (Fin.tail z) = 0 ∧ B (Fin.tail z) = 0)
      let R1 : Finset (Fin (n + 1) → K) := Z.filter
        (fun z => ¬ (A (Fin.tail z) = 0 ∧ B (Fin.tail z) = 0))
      have hcons (z : Fin (n + 1) → K) : z = Fin.cons (z 0) (Fin.tail z) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      have hR0sub : R0 ⊆ Z := by
        intro z hz
        have hb := (Finset.mem_filter.mp hz).2
        rw [hcons z]
        simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
        change (1 - z 0) * A (Fin.tail z) + z 0 * B (Fin.tail z) = 0
        rw [hb.1, hb.2]
        ring
      have hR0card : R0.card = Fintype.card K * Both.card := by
        let P : (Fin (n + 1) → K) → Prop :=
          fun z => A (Fin.tail z) = 0 ∧ B (Fin.tail z) = 0
        have hfilter : R0 = Finset.univ.filter P := by
          ext z
          simp [R0, P]
        calc
          _ = (Finset.univ.filter P).card := by rw [hfilter]
          _ = Fintype.card K * Both.card := by
            have hc := filter_card_fin_cons (K := K) n P
            convert hc using 1
            · congr 1
              ext z
              simp [P]
            · simp [Both, P, Fin.tail_cons]
      have hBoth : Both ⊆ Gzero := by
        intro v hv
        have hb := (Finset.mem_filter.mp hv).2
        simp only [Gzero, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hbit : b 0
        · simpa [g, hbit] using hb.2
        · simpa [g, hbit] using hb.1
      have hR1maps : Set.MapsTo Fin.tail (R1 : Set (Fin (n + 1) → K))
          ((Finset.univ : Finset (Fin n → K)) : Set (Fin n → K)) := by
        intro z hz
        simp
      have hR1inj : (R1 : Set (Fin (n + 1) → K)).InjOn Fin.tail := by
        intro z hz w hw htailEq
        have hzroot : R0P.Sumcheck.mle (n + 1) f z = 0 :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
        have hwroot : R0P.Sumcheck.mle (n + 1) f w = 0 :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
        have hznot : ¬ (A (Fin.tail z) = 0 ∧ B (Fin.tail z) = 0) :=
          (Finset.mem_filter.mp hz).2
        have hnonzero : A (Fin.tail z) ≠ 0 ∨ B (Fin.tail z) ≠ 0 :=
          not_and_or.mp hznot
        have hzlin : A (Fin.tail z) + z 0 * (B (Fin.tail z) - A (Fin.tail z)) = 0 := by
          rw [R0P.Sumcheck.mle] at hzroot
          change (1 - z 0) * A (Fin.tail z) + z 0 * B (Fin.tail z) = 0 at hzroot
          have hrec : (1-z 0) * A (Fin.tail z) + z 0 * B (Fin.tail z) = 0 := hzroot
          calc
            _ = (1-z 0) * A (Fin.tail z) + z 0 * B (Fin.tail z) := by ring
            _ = 0 := hrec
        have hwlin : A (Fin.tail z) + w 0 * (B (Fin.tail z) - A (Fin.tail z)) = 0 := by
          rw [R0P.Sumcheck.mle] at hwroot
          change (1 - w 0) * A (Fin.tail w) + w 0 * B (Fin.tail w) = 0 at hwroot
          have hrec : (1-w 0) * A (Fin.tail w) + w 0 * B (Fin.tail w) = 0 := hwroot
          rw [← htailEq] at hrec
          calc
            _ = (1-w 0) * A (Fin.tail z) + w 0 * B (Fin.tail z) := by ring
            _ = 0 := hrec
        have hhead : z 0 = w 0 :=
          affine_zero_unique (A (Fin.tail z)) (B (Fin.tail z)) (z 0) (w 0)
            hzlin hwlin hnonzero
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hhead
        · exact congrFun htailEq j
      have hR1 : R1.card ≤ Fintype.card (Fin n → K) :=
        Finset.card_le_card_of_injOn Fin.tail hR1maps hR1inj
      have hGzero : Gzero.card ≤ n * Fintype.card K ^ (n - 1) := htail
      have hdisj : Disjoint R0 R1 := by
        rw [Finset.disjoint_left]
        intro z hz0 hz1
        exact (Finset.mem_filter.mp hz1).2 (Finset.mem_filter.mp hz0).2
      have hpart : Z = R0 ∪ R1 := by
        ext z
        constructor
        · intro hz
          by_cases hb0 : A (Fin.tail z) = 0 ∧ B (Fin.tail z) = 0
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, hb0⟩))
        · intro hz
          rcases Finset.mem_union.mp hz with hz0 | hz1
          · exact hR0sub hz0
          · exact (Finset.mem_filter.mp hz1).1
      calc
        _ = Z.card := rfl
        _ = R0.card + R1.card := by rw [hpart, Finset.card_union_of_disjoint hdisj]
        _ ≤ Fintype.card K * Gzero.card + Fintype.card (Fin n → K) := by
          rw [hR0card]
          exact Nat.add_le_add
            (Nat.mul_le_mul_left _ (Finset.card_le_card hBoth)) hR1
        _ ≤ Fintype.card K * (n * Fintype.card K ^ (n - 1)) + Fintype.card K ^ n := by
          simpa [Fintype.card_fun] using Nat.add_le_add_right
            (Nat.mul_le_mul_left (Fintype.card K) hGzero) (Fintype.card K ^ n)
        _ ≤ (n + 1) * Fintype.card K ^ n := by
          cases n with
          | zero => simp
          | succ n =>
              simp only [Nat.succ_sub_one, pow_succ]
              exact le_of_eq (by ring)

#print axioms mle_bad_card_of_witness

theorem mle_bad_card (n : Nat) (f : (Fin n → Bool) → K) (hf : f ≠ 0) :
    (Finset.univ.filter (fun z : Fin n → K => R0P.Sumcheck.mle n f z = 0)).card ≤
      n * Fintype.card K ^ (n - 1) := by
  apply mle_bad_card_of_witness n f
  by_contra hnone
  have hzero : ∀ b, f b = 0 := by
    intro b
    by_contra hb
    exact hnone ⟨b, hb⟩
  apply hf
  funext b
  exact hzero b

#print axioms mle_bad_card

theorem badZc_card (f : (Fin 10 → Bool) → K) :
    (Finset.univ.filter (fun z : Fin 10 → K => R0P.Sumcheck.BadZc f z)).card ≤
      10 * Fintype.card K ^ 9 := by
  classical
  by_cases hf : ∃ b, f b ≠ 0
  · have h := mle_bad_card_of_witness 10 f hf
    simpa [R0P.Sumcheck.BadZc, hf] using h
  · have hempty : (Finset.univ.filter
        (fun z : Fin 10 → K => R0P.Sumcheck.BadZc f z)) = ∅ := by
      ext z
      simp [R0P.Sumcheck.BadZc, hf]
    rw [hempty]
    simp

#print axioms badZc_card

end

end R0P.SemBadSets

set_option autoImplicit false

noncomputable section

namespace R0P.SemBadSets

open Polynomial
open R0P.Sumcheck

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The first `i` coordinates of a challenge vector, in the explicit
`Fin.castLE` embedding used by an adaptive prover strategy. -/
def strategyPrefix {n : Nat} (α : Fin n → K) (i : Fin n) : Fin i.val → K :=
  fun j => α (Fin.castLE i.isLt.le j)

#print axioms strategyPrefix

/-- Round polynomials selected from the strategy using the transcript prefix. -/
def strategyPolys {n : Nat}
    (strat : (i : Fin n) → (Fin i.val → K) → K[X]) (α : Fin n → K) : Fin n → K[X] :=
  fun i => strat i (strategyPrefix α i)

#print axioms strategyPolys

/-- The adaptive transcript is checked by ordinary sumcheck acceptance after
instantiating each round polynomial at its actual earlier-challenge prefix. -/
def strategyAccept (d n : Nat) (G : (Fin n → K) → K) (c : K)
    (strat : (i : Fin n) → (Fin i.val → K) → K[X]) (α : Fin n → K) : Prop :=
  accept d n G c (strategyPolys strat α) α

#print axioms strategyAccept

/-- Accepted transcripts with a false initial claim. -/
def badAlphaStrategy (d n : Nat) (G : (Fin n → K) → K) (c : K)
    (strat : (i : Fin n) → (Fin i.val → K) → K[X]) (α : Fin n → K) : Prop :=
  strategyAccept d n G c strat α ∧ bsum n G ≠ c

#print axioms badAlphaStrategy

omit [Field K] in
private theorem strategyPrefix_cons_succ (n : Nat) (x : K)
    (α : Fin n → K) (i : Fin n) :
    strategyPrefix (Fin.cons x α) i.succ =
      (Fin.cons x (strategyPrefix α i) : Fin (i.val+1) → K) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · change (Fin.cons x α : Fin (n+1) → K) 0 =
      (Fin.cons x (strategyPrefix α i) : Fin (i.val+1) → K) 0
    simp only [Fin.cons_zero]
  · intro j
    change (Fin.cons x α : Fin (n+1) → K) (Fin.castLE i.isLt.le j).succ =
      (Fin.cons x (strategyPrefix α i) : Fin (i.val+1) → K) j.succ
    simp only [Fin.cons_succ]
    rfl

#print axioms strategyPrefix_cons_succ

private theorem strategyPolys_tail (n : Nat) (x : K)
    (strat : (i : Fin (n+1)) → (Fin i.val → K) → K[X]) (α : Fin n → K) :
    Fin.tail (strategyPolys strat (Fin.cons x α)) =
      strategyPolys (fun i pref => strat i.succ (Fin.cons x pref)) α := by
  funext i
  change strat i.succ (strategyPrefix (Fin.cons x α) i.succ) =
    strat i.succ (Fin.cons x (strategyPrefix α i))
  rw [strategyPrefix_cons_succ]
  rfl

#print axioms strategyPolys_tail

private theorem strategyAccept_cons_iff (d n : Nat) (G : (Fin (n+1) → K) → K)
    (c x : K) (strat : (i : Fin (n+1)) → (Fin i.val → K) → K[X])
    (α : Fin n → K) :
    strategyAccept d (n+1) G c strat (Fin.cons x α) ↔
      (strat 0 (fun j => j.elim0)).natDegree ≤ d ∧
      (strat 0 (fun j => j.elim0)).eval 0 +
        (strat 0 (fun j => j.elim0)).eval 1 = c ∧
    strategyAccept d n (fun v => G (Fin.cons x v))
      ((strat 0 (fun j => j.elim0)).eval x)
      (fun i pref => strat i.succ (Fin.cons x pref)) α := by
  have hzero : strategyPrefix (Fin.cons x α) (0 : Fin (n+1)) =
      (fun j => j.elim0) := by
    funext j
    exact j.elim0
  have hhead : (strategyPolys strat (Fin.cons x α)) 0 =
      strat 0 (fun j => j.elim0) := by
    change strat 0 (strategyPrefix (Fin.cons x α) 0) = _
    rw [hzero]
  simp only [strategyAccept, accept]
  rw [hhead, strategyPolys_tail, Fin.tail_cons, Fin.cons_zero]

#print axioms strategyAccept_cons_iff

/-- A false accepted claim under an adaptive degree-bounded strategy has at
most `n*d*|K|^(n-1)` challenge vectors. The round polynomial is queried at
`strategyPrefix`, i.e. `α (Fin.castLE i.isLt.le j)` for each prior coordinate. -/
theorem adaptive_strategy_bad_card [Fintype K] : ∀ (n d : Nat)
    (G : (Fin n → K) → K) (c : K)
    (strat : (i : Fin n) → (Fin i.val → K) → K[X]),
    IndDeg d n G →
    Fintype.card {α : Fin n → K // badAlphaStrategy d n G c strat α} ≤
      n * d * Fintype.card K ^ (n - 1) := by
  classical
  intro n
  induction n with
  | zero =>
      intro d G c strat hdeg
      simp [badAlphaStrategy, strategyAccept, Sumcheck.accept, bsum]
  | succ n ih =>
      intro d G c strat hdeg
      let event : (Fin (n+1) → K) → Prop := badAlphaStrategy d (n+1) G c strat
      by_cases hevent : ∃ α, event α
      · obtain ⟨α₀, hα₀⟩ := hevent
        let x₀ := α₀ 0
        let v₀ := Fin.tail α₀
        have hα₀eq : α₀ = Fin.cons x₀ v₀ := by
          funext i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            rfl
        have hchosen : event (Fin.cons x₀ v₀) := by
          rw [← hα₀eq]
          exact hα₀
        obtain ⟨⟨h, hhd, hh⟩, hrest⟩ := hdeg
        let p := strat 0 (fun j => j.elim0)
        have hhead := (strategyAccept_cons_iff d n G _ x₀ strat v₀).1 hchosen.1
        have hpdeg : p.natDegree ≤ d := by simpa [p] using hhead.1
        have hsum : p.eval 0 + p.eval 1 = c := by simpa [p] using hhead.2.1
        have hph : p ≠ h := by
          intro heq
          apply hchosen.2
          calc
            bsum (n+1) G =
                bsum n (fun v => G (Fin.cons 0 v)) +
                  bsum n (fun v => G (Fin.cons 1 v)) := by rw [bsum]
            _ = h.eval 0 + h.eval 1 := by rw [hh 0, hh 1]
            _ = p.eval 0 + p.eval 1 := by rw [heq]
            _ = c := hsum
        have hdiff : p - h ≠ 0 := sub_ne_zero.mpr hph
        have hdifdeg : (p - h).natDegree ≤ d :=
          (natDegree_sub_le _ _).trans (max_le hpdeg hhd)
        let roots : Finset K := Finset.univ.filter (fun x => (p - h).eval x = 0)
        have hroots : roots.card ≤ d :=
          univariate_bad_card (p - h) hdiff d hdifdeg
        let q := Fintype.card K
        have hfiber (x : K) :
            Fintype.card {v : Fin n → K // event (Fin.cons x v)} ≤
              if x ∈ roots then q ^ n else n * d * q ^ (n - 1) := by
          by_cases hx : x ∈ roots
          · rw [if_pos hx]
            calc
              _ ≤ Fintype.card (Fin n → K) :=
                Fintype.card_le_of_injective (fun v => v.1) Subtype.val_injective
              _ = q ^ n := by simp [q]
          · rw [if_neg hx]
            have hfalseSuffix :
                bsum n (fun v => G (Fin.cons x v)) ≠ p.eval x := by
              intro heq
              apply hx
              simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [eval_sub, hh x, heq, sub_self]
            let sfx : (i : Fin n) → (Fin i.val → K) → K[X] :=
              fun i pref => strat i.succ (Fin.cons x pref)
            have hsub : ∀ v, event (Fin.cons x v) →
                badAlphaStrategy d n (fun w => G (Fin.cons x w)) (p.eval x) sfx v := by
              intro v hv
              have hc := (strategyAccept_cons_iff d n G _ x strat v).1 hv.1
              exact ⟨hc.2.2, hfalseSuffix⟩
            have hinj : Function.Injective
                (fun v : {v : Fin n → K // event (Fin.cons x v)} =>
                  (⟨v.1, hsub v.1 v.2⟩ :
                    {v : Fin n → K // badAlphaStrategy d n
                      (fun w => G (Fin.cons x w)) (p.eval x) sfx v})) := by
              intro a b hab
              have hval : a.1 = b.1 :=
                congrArg (fun z : {w : Fin n → K // badAlphaStrategy d n
                  (fun w => G (Fin.cons x w)) (p.eval x) sfx w} => z.1) hab
              exact Subtype.ext hval
            calc
              _ ≤ Fintype.card {v : Fin n → K //
                  badAlphaStrategy d n (fun w => G (Fin.cons x w)) (p.eval x) sfx v} :=
                Fintype.card_le_of_injective _ hinj
              _ ≤ n * d * q ^ (n - 1) := ih d _ _ _ (hrest x)
        have hsplit : Fintype.card {α : Fin (n+1) → K // event α} =
            ∑ x : K, Fintype.card {v : Fin n → K // event (Fin.cons x v)} := by
          simpa only [← Fintype.card_subtype] using
            (filter_card_fin_cons (K := K) n event)
        rw [hsplit]
        calc
          (∑ x : K, Fintype.card {v : Fin n → K // event (Fin.cons x v)}) ≤
              ∑ x : K, (if x ∈ roots then q ^ n else n * d * q ^ (n - 1)) :=
            Finset.sum_le_sum (fun x hx => hfiber x)
          _ = roots.card * q ^ n +
              (Finset.univ.filter (fun x : K => x ∉ roots)).card *
                (n * d * q ^ (n - 1)) := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
              (p := fun x : K => x ∈ roots)]
            have hrootSet :
                Finset.univ.filter (fun x : K => x ∈ roots) = roots := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hrootSum :
                (∑ x ∈ Finset.univ.filter (fun x : K => x ∈ roots),
                  if x ∈ roots then q ^ n else n * d * q ^ (n - 1)) =
                  roots.card * q ^ n := by
              rw [hrootSet]
              calc
                _ = ∑ x ∈ roots, q ^ n := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  simp [hx]
                _ = _ := by simp
            have hnonrootSum :
                (∑ x ∈ Finset.univ.filter (fun x : K => x ∉ roots),
                  if x ∈ roots then q ^ n else n * d * q ^ (n - 1)) =
                  (Finset.univ.filter (fun x : K => x ∉ roots)).card *
                    (n * d * q ^ (n - 1)) := by
              calc
                _ = ∑ x ∈ Finset.univ.filter (fun x : K => x ∉ roots),
                    (n * d * q ^ (n - 1)) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hnot : x ∉ roots := (Finset.mem_filter.mp hx).2
                  simp [hnot]
                _ = _ := by simp
            rw [hrootSum, hnonrootSum]
          _ ≤ d * q ^ n + q * (n * d * q ^ (n - 1)) := by
            apply Nat.add_le_add
            · exact Nat.mul_le_mul_right _ hroots
            · exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
          _ = (n+1) * d * q ^ n := by
            by_cases hn : n = 0
            · simp [hn]
            · have hpow : q * q ^ (n - 1) = q ^ n := by
                obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
                simp [pow_succ, Nat.mul_comm]
              calc
                _ = d * q ^ n + n * d * (q * q ^ (n - 1)) := by ring
                _ = d * q ^ n + n * d * q ^ n := by rw [hpow]
                _ = (n+1) * d * q ^ n := by ring
      · have hempty : ∀ α, ¬ event α := by
          intro α hα
          exact hevent ⟨α, hα⟩
        letI : IsEmpty {α : Fin (n+1) → K // event α} :=
          ⟨fun a => (hempty a.1 a.2).elim⟩
        simp

#print axioms adaptive_strategy_bad_card

/-- The fixed production ledger instance: ten adaptive sumcheck rounds and
individual round degree at most 27. -/
theorem badAlpha_strategy [Fintype K]
    (G : (Fin 10 → K) → K)
    (strat : (i : Fin 10) → (Fin i.val → K) → K[X])
    (hdeg : IndDeg 27 10 G) :
    (Finset.univ.filter (fun α : Fin 10 → K =>
      accept 27 10 G 0
        (fun i => strat i (fun j => α (Fin.castLE i.isLt.le j))) α ∧
      bsum 10 G ≠ 0)).card ≤ 10 * 27 * Fintype.card K ^ 9 := by
  have hbound : (Finset.univ.filter (fun α : Fin 10 → K =>
      badAlphaStrategy 27 10 G 0 strat α)).card ≤
      10 * 27 * Fintype.card K ^ 9 := by
    simpa only [Fintype.card_subtype] using
      adaptive_strategy_bad_card (K := K) 10 27 G 0 strat hdeg
  have hfilters :
      Finset.univ.filter (fun α : Fin 10 → K => badAlphaStrategy 27 10 G 0 strat α) =
      Finset.univ.filter (fun α : Fin 10 → K =>
        accept 27 10 G 0
          (fun i => strat i (fun j => α (Fin.castLE i.isLt.le j))) α ∧
        bsum 10 G ≠ 0) := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      badAlphaStrategy, strategyAccept]
    unfold strategyPolys strategyPrefix
    rfl
  rw [← congrArg Finset.card hfilters]
  exact hbound

#print axioms badAlpha_strategy

end R0P.SemBadSets

end

-- Final public statement audit for the fixed composition obligations.
#check @R0P.SemBadSets.badMu_card
#check @R0P.SemBadSets.badTheta_card
#check @R0P.SemBadSets.mle_bad_card
#check @R0P.SemBadSets.badZc_card
#check @R0P.SemBadSets.badAlpha_strategy
#check @R0P.SemBadSets.MLDeg
#check @R0P.SemBadSets.mlDeg_indDeg
#check @R0P.SemBadSets.indDeg_of_multilinear_product
#check @R0P.SemBadSets.mlDeg_add
#check @R0P.SemBadSets.mlDeg_mul
#check @R0P.SemBadSets.mlDeg_smul
#check @R0P.SemBadSets.mlDeg_eqwB
#check @R0P.SemBadSets.mlDeg_mle

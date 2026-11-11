import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! The Aspis one-transaction verifier: the final sumcheck over the final
message, the combining challenge for its two claims, and their composition
with the batched first-fold check. (File and theorem names keep the
experiment's labels "stage C" for the batched first-fold check and "stage D"
for the final sumcheck.)

Kind of result: every theorem here is a MATHEMATICAL MODEL THEOREM about fixed
objects (vectors, polynomials, finite sets) over arbitrary fields `K`, `E` with
an embedding `iota : K →+* E` (in the protocol `K` = QM31, `E` = WideExact).
None is a source-helper theorem, a source-to-model refinement, a Fiat--Shamir
or probability statement, or connected to any release artifact. What would
connect each definition to `crates/aspis-r1-cost-probe/src/fused.rs` and
`weights.rs` is listed in `../SOUNDNESS-ARGUMENT.md`, where it is OPEN.

Contents.
* Section A: root counting (copied from `TwoFamilyResidualBatch.lean`, same
  proofs, so this file compiles alone).
* Section B: fold, iterated fold and the multilinear-extension identities
  (`foldAll_zero_eq_sum`, `sum_eqw_bitProd`, `query_weight_extension`,
  `sum_eqw_digits3`, `digit_weights`, `sum_grouped`, `sum_range_support`).
* Section C: one sumcheck round as coded (`proverPoly_eval`,
  `roundBad_card_le_two`, `round_doom_persists`,
  `roundBad_contains_every_coincidence`) and the chain (`sumcheck_sound`).
* Section D: the combining challenge (`lambdaBad_card_le_one`, `lambda_sound`).
* Section E: the residual pair under the batching challenge (`bad2`,
  `bad2_card_le_21`).
* Section F: the composed statement (`stageCD_sound`).
* Section G: start-count arithmetic (`starts35_exceed`, `new_row_cap_le_B`,
  `perKind_margin`, `ceil_mass_le`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AspisFuture.StageD

open Polynomial Finset
open scoped BigOperators

noncomputable section

variable {K E : Type} [Field K] [Field E] [Fintype K]

local instance : DecidableEq K := Classical.decEq K
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-! ## A. Root counting -/

/-- A nonzero polynomial over `E` has at most its degree many roots among the
images of `K`. -/
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

/-! ## B. Folding and multilinear extensions -/

/-- Splitting a sum over `2 * N` indices into consecutive pairs. -/
theorem sum_range_two_mul (N : ℕ) (h : ℕ → E) :
    ∑ j ∈ range (2 * N), h j = ∑ m ∈ range N, (h (2 * m) + h (2 * m + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- One fold at challenge `r`, pairing positions `2m` and `2m+1` (bit 0 first).
This is the prover's update in `stage_d_rounds`
(`f[2m] + (f[2m+1] - f[2m]) * r`). -/
def fold (r : E) (v : ℕ → E) : ℕ → E :=
  fun m => v (2 * m) + r * (v (2 * m + 1) - v (2 * m))

/-- Folding at the challenges in order (round 0 binds bit 0). -/
def foldAll (iota : K →+* E) : List K → (ℕ → E) → (ℕ → E)
  | [], v => v
  | r :: rs, v => foldAll iota rs (fold (iota r) v)

/-- The equality weight of index `j` at the point `rs`: bit `b` of `j` selects
`r_b` (set) or `1 - r_b` (clear). This is `eq[j]` of `equality_tables`. -/
def eqw (iota : K →+* E) : List K → ℕ → E
  | [], _ => 1
  | r :: rs, j => (if j % 2 = 1 then iota r else 1 - iota r) * eqw iota rs (j / 2)

/-- The iterated fold at position 0 is the multilinear extension
`sum_j v_j * eq_j(r)`. -/
theorem foldAll_zero_eq_sum (iota : K →+* E) :
    ∀ (rs : List K) (v : ℕ → E),
      foldAll iota rs v 0 = ∑ j ∈ range (2 ^ rs.length), v j * eqw iota rs j
  | [], v => by simp [foldAll, eqw]
  | r :: rs, v => by
    rw [foldAll, foldAll_zero_eq_sum iota rs, List.length_cons, pow_succ',
      sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro m _
    have h1 : ¬ (2 * m % 2 = 1) := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    have h3 : 2 * m / 2 = m := by omega
    have h4 : (2 * m + 1) / 2 = m := by omega
    simp only [fold, eqw, if_neg h1, if_pos h2, h3, h4]
    ring

/-- Folding is linear, hence so is the iterated fold. -/
theorem foldAll_add_mul (iota : K →+* E) :
    ∀ (rs : List K) (a b : ℕ → E) (c : E) (m : ℕ),
      foldAll iota rs (fun j => a j + c * b j) m =
        foldAll iota rs a m + c * foldAll iota rs b m
  | [], _, _, _, _ => rfl
  | r :: rs, a, b, c, m => by
    simp only [foldAll]
    have hfold : fold (iota r) (fun j => a j + c * b j) =
        fun j => fold (iota r) a j + c * fold (iota r) b j := by
      funext j
      simp only [fold]
      ring
    rw [hfold]
    exact foldAll_add_mul iota rs _ _ c m

/-- Product over the set bits of `j` of the entries of `ts` (bit 0 first). With
`ts = [t_0, ..., t_5]` and `t_{b+1} = 2 t_b^2 - 1` this is the query weight
`basis_j(x)` of `accumulate_weights`. -/
def bitProd : List E → ℕ → E
  | [], _ => 1
  | t :: ts, j => (if j % 2 = 1 then t else 1) * bitProd ts (j / 2)

/-- Product form of the extension of a bit-product vector: the identity that
`query_weight_mle` evaluates, `prod_b (1 + r_b (t_b - 1))`. -/
theorem sum_eqw_bitProd (iota : K →+* E) :
    ∀ (rs : List K) (ts : List E), rs.length = ts.length →
      ∑ j ∈ range (2 ^ rs.length), eqw iota rs j * bitProd ts j =
        (List.zipWith (fun r t => 1 + iota r * (t - 1)) rs ts).prod
  | [], [], _ => by simp [eqw, bitProd]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | r :: rs, t :: ts, h => by
    have hl : rs.length = ts.length := by simpa using h
    rw [List.length_cons, pow_succ', sum_range_two_mul, List.zipWith_cons_cons,
      List.prod_cons, ← sum_eqw_bitProd iota rs ts hl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have h1 : ¬ (2 * m % 2 = 1) := by omega
    have h2 : (2 * m + 1) % 2 = 1 := by omega
    have h3 : 2 * m / 2 = m := by omega
    have h4 : (2 * m + 1) / 2 = m := by omega
    simp only [eqw, bitProd, if_neg h1, if_pos h2, h3, h4]
    ring

/-- The query weight vector `w_j = sum_i rho^i basis_j(x_i)` has extension
`sum_i rho^i prod_b (1 + r_b (t_b(x_i) - 1))` (linearity plus the product form). -/
theorem query_weight_extension (iota : K →+* E) (rs : List K) (n : ℕ)
    (coef : Fin n → E) (ts : Fin n → List E) (hts : ∀ i, rs.length = (ts i).length) :
    ∑ j ∈ range (2 ^ rs.length), (∑ i : Fin n, coef i * bitProd (ts i) j) * eqw iota rs j =
      ∑ i : Fin n, coef i *
        (List.zipWith (fun r t => 1 + iota r * (t - 1)) rs (ts i)).prod := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sum_eqw_bitProd iota rs (ts i) (hts i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Splitting a sum over `4 * N` indices into consecutive quadruples. -/
theorem sum_range_four_mul (N : ℕ) (h : ℕ → E) :
    ∑ j ∈ range (4 * N), h j =
      ∑ k ∈ range N, (h (4 * k) + h (4 * k + 1) + h (4 * k + 2) + h (4 * k + 3)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- One base-four digit (bits `2d`, `2d+1`) factors out of the extension. The
first factor is the four-term sum of `Weights::mle_at` against
`digits[d] = [(1-a)(1-b), a(1-b), (1-a)b, ab]`. -/
theorem sum_eqw_digit (iota : K →+* E) (a b : K) (rs : List K) (h G : ℕ → E) :
    ∑ j ∈ range (2 ^ (rs.length + 2)), eqw iota (a :: b :: rs) j * (h (j % 4) * G (j / 4)) =
      (∑ m ∈ range 4, eqw iota [a, b] m * h m) *
        ∑ j ∈ range (2 ^ rs.length), eqw iota rs j * G j := by
  rw [show 2 ^ (rs.length + 2) = 4 * 2 ^ rs.length by ring, sum_range_four_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have e0 : ¬ (4 * k % 2 = 1) := by omega
  have e1 : (4 * k + 1) % 2 = 1 := by omega
  have e2 : ¬ ((4 * k + 2) % 2 = 1) := by omega
  have e3 : (4 * k + 3) % 2 = 1 := by omega
  have d0 : 4 * k / 2 = 2 * k := by omega
  have d1 : (4 * k + 1) / 2 = 2 * k := by omega
  have d2 : (4 * k + 2) / 2 = 2 * k + 1 := by omega
  have d3 : (4 * k + 3) / 2 = 2 * k + 1 := by omega
  have f0 : ¬ (2 * k % 2 = 1) := by omega
  have f1 : (2 * k + 1) % 2 = 1 := by omega
  have g0 : 2 * k / 2 = k := by omega
  have g1 : (2 * k + 1) / 2 = k := by omega
  have m0 : 4 * k % 4 = 0 := by omega
  have m1 : (4 * k + 1) % 4 = 1 := by omega
  have m2 : (4 * k + 2) % 4 = 2 := by omega
  have m3 : (4 * k + 3) % 4 = 3 := by omega
  have q0 : 4 * k / 4 = k := by omega
  have q1 : (4 * k + 1) / 4 = k := by omega
  have q2 : (4 * k + 2) / 4 = k := by omega
  have q3 : (4 * k + 3) / 4 = k := by omega
  simp only [eqw, if_neg e0, if_pos e1, if_neg e2, if_pos e3, d0, d1, d2, d3,
    if_neg f0, if_pos f1, g0, g1, m0, m1, m2, m3, q0, q1, q2, q3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- Three digits: the extension of a product-row vector
`h0(d_0(j)) * h1(d_1(j)) * h2(d_2(j))` over six bits is the product of three
four-term sums (rows 1, 2, 3, 5, 6 of `Weights::mle_at`, before the scale). -/
theorem sum_eqw_digits3 (iota : K →+* E) (r0 r1 r2 r3 r4 r5 : K) (h0 h1 h2 : ℕ → E) :
    ∑ j ∈ range (2 ^ 6), eqw iota [r0, r1, r2, r3, r4, r5] j *
        (h0 (j % 4) * (h1 (j / 4 % 4) * (h2 (j / 4 / 4 % 4) * 1))) =
      (∑ m ∈ range 4, eqw iota [r0, r1] m * h0 m) *
        ((∑ m ∈ range 4, eqw iota [r2, r3] m * h1 m) *
          (∑ m ∈ range 4, eqw iota [r4, r5] m * h2 m)) := by
  have step := sum_eqw_digit iota r0 r1 [r2, r3, r4, r5] h0
    (fun j => h1 (j % 4) * (h2 (j / 4 % 4) * 1))
  have step2 := sum_eqw_digit iota r2 r3 [r4, r5] h1 (fun j => h2 (j % 4) * 1)
  have step3 := sum_eqw_digit iota r4 r5 [] h2 (fun _ => 1)
  simp only [List.length_cons, List.length_nil] at step step2 step3
  rw [step, step2, step3]
  simp [eqw]

/-- The four digit weights are the bit-pair equality weights of
`equality_tables`: `[(1-a)(1-b), a(1-b), (1-a)b, ab]`. -/
theorem digit_weights (iota : K →+* E) (a b : K) :
    eqw iota [a, b] 0 = (1 - iota a) * (1 - iota b) ∧
    eqw iota [a, b] 1 = iota a * (1 - iota b) ∧
    eqw iota [a, b] 2 = (1 - iota a) * iota b ∧
    eqw iota [a, b] 3 = iota a * iota b := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [eqw]

/-- A vector constant on groups (the inactive row): its extension is the sum
over groups of the group weight times the summed equality weights of the
group, which is how `Weights::mle_at` evaluates row 0. -/
theorem sum_grouped (N G : ℕ) (group : ℕ → ℕ) (hgroup : ∀ j ∈ range N, group j ∈ range G)
    (weight : ℕ → E) (e : ℕ → E) :
    ∑ j ∈ range N, weight (group j) * e j =
      ∑ g ∈ range G, weight g * ∑ j ∈ (range N).filter (fun j => group j = g), e j := by
  rw [← Finset.sum_fiberwise_of_maps_to hgroup]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

/-- A vector supported on the first `n` positions (the Libra row, `n = 4`). -/
theorem sum_range_support (n N : ℕ) (hn : n ≤ N) (v : ℕ → E) (hv : ∀ j, n ≤ j → v j = 0)
    (e : ℕ → E) :
    ∑ j ∈ range N, v j * e j = ∑ j ∈ range n, v j * e j := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hn)
  intro j hjN hjn
  rw [hv j (by simpa using hjn), zero_mul]

/-! ## C. Sumcheck rounds -/

/-- The degree-one polynomial through `(0, a)` and `(1, b)`. -/
def lin (a b : E) : E[X] := C (b - a) * X + C a

theorem lin_eval (a b x : E) : (lin a b).eval x = a + x * (b - a) := by
  simp [lin]
  ring

theorem lin_natDegree (a b : E) : (lin a b).natDegree ≤ 1 :=
  Polynomial.natDegree_linear_le

/-- The true round polynomial of `sum_{j < 2N} f_j u_j` with bit 0 free. -/
def roundPoly (N : ℕ) (f u : ℕ → E) : E[X] :=
  ∑ m ∈ range N, lin (f (2 * m)) (f (2 * m + 1)) * lin (u (2 * m)) (u (2 * m + 1))

theorem roundPoly_natDegree_le (N : ℕ) (f u : ℕ → E) : (roundPoly N f u).natDegree ≤ 2 := by
  unfold roundPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (by
    have := lin_natDegree (f (2 * m)) (f (2 * m + 1))
    have := lin_natDegree (u (2 * m)) (u (2 * m + 1))
    omega)

theorem roundPoly_sum (N : ℕ) (f u : ℕ → E) :
    (roundPoly N f u).eval 0 + (roundPoly N f u).eval 1 =
      ∑ j ∈ range (2 * N), f j * u j := by
  rw [sum_range_two_mul]
  unfold roundPoly
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Polynomial.eval_mul, lin_eval]
  ring

theorem roundPoly_eval (N : ℕ) (f u : ℕ → E) (r : E) :
    (roundPoly N f u).eval r = ∑ m ∈ range N, fold r f m * fold r u m := by
  unfold roundPoly
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Polynomial.eval_mul, lin_eval, fold]

/-- The prover's round polynomial: constant `c0`, quadratic `c2`, and the
linear coefficient the verifier derives, `c1 = cl - c0 - c0 - c2`. -/
def proverPoly (cl c0 c2 : E) : E[X] := C c2 * X ^ 2 + C (cl - c0 - c0 - c2) * X + C c0

/-- The verifier's update in `summed_final_checks`: `c0 + (c1 + c2 r) r`. -/
theorem proverPoly_eval (cl c0 c2 x : E) :
    (proverPoly cl c0 c2).eval x = c0 + ((cl - c0 - c0 - c2) + c2 * x) * x := by
  simp [proverPoly]
  ring

theorem proverPoly_sum (cl c0 c2 : E) :
    (proverPoly cl c0 c2).eval 0 + (proverPoly cl c0 c2).eval 1 = cl := by
  rw [proverPoly_eval, proverPoly_eval]
  ring

theorem proverPoly_natDegree (cl c0 c2 : E) : (proverPoly cl c0 c2).natDegree ≤ 2 :=
  Polynomial.natDegree_quadratic_le

/-- Bad challenges of one round, a function of the round's prefix only: the
true round polynomial `g`, the running claim `cl` and the prover's `(c0, c2)`.
Empty when the claim is true; otherwise the challenges at which the prover's
polynomial meets the true one. -/
def roundBad (iota : K →+* E) (g : E[X]) (cl c0 c2 : E) : Finset K :=
  if g.eval 0 + g.eval 1 = cl then ∅
  else Finset.univ.filter (fun r : K => (proverPoly cl c0 c2).eval (iota r) = g.eval (iota r))

/-- At most two bad challenges per round (degree at most 2 over `E`, challenge
in `K`). -/
theorem roundBad_card_le_two (iota : K →+* E) (g : E[X]) (hg : g.natDegree ≤ 2)
    (cl c0 c2 : E) : (roundBad iota g cl c0 c2).card ≤ 2 := by
  unfold roundBad
  split_ifs with h
  · simp
  · have hne : proverPoly cl c0 c2 - g ≠ 0 := by
      intro h0
      apply h
      have hev := congrArg (fun p : E[X] => p.eval 0 + p.eval 1) h0
      simp only [Polynomial.eval_sub, Polynomial.eval_zero] at hev
      linear_combination (proverPoly_sum cl c0 c2) - hev
    have hdeg : (proverPoly cl c0 c2 - g).natDegree ≤ 2 :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le (proverPoly_natDegree cl c0 c2) hg)
    calc
      (Finset.univ.filter (fun r : K =>
          (proverPoly cl c0 c2).eval (iota r) = g.eval (iota r))).card
          ≤ (Finset.univ.filter (fun r : K =>
              (proverPoly cl c0 c2 - g).eval (iota r) = 0)).card := by
            apply Finset.card_le_card
            intro r hr
            rw [Finset.mem_filter] at hr ⊢
            refine ⟨hr.1, ?_⟩
            rw [Polynomial.eval_sub, hr.2, sub_self]
      _ ≤ (proverPoly cl c0 c2 - g).natDegree :=
            subfield_roots_card_le_natDegree iota _ hne
      _ ≤ 2 := hdeg

/-- Outside the round's bad set a false claim stays false. -/
theorem round_doom_persists (iota : K →+* E) (g : E[X]) (cl c0 c2 : E) (r : K)
    (hfalse : g.eval 0 + g.eval 1 ≠ cl) (hr : r ∉ roundBad iota g cl c0 c2) :
    (proverPoly cl c0 c2).eval (iota r) ≠ g.eval (iota r) := by
  intro heq
  apply hr
  unfold roundBad
  rw [if_neg hfalse, Finset.mem_filter]
  exact ⟨Finset.mem_univ r, heq⟩

/-- The R547/R548 check. When the running claim is already false, EVERY
challenge at which the reconstructed polynomial (linear coefficient rebuilt
from the claim, `c0` and `c2`, as coded) meets the true round polynomial is in
the charged bad set, the values 0 and 1 included; there is no uncharged
coincidence. -/
theorem roundBad_contains_every_coincidence (iota : K →+* E) (g : E[X]) (cl c0 c2 : E)
    (hfalse : g.eval 0 + g.eval 1 ≠ cl) (r : K)
    (hmeet : (proverPoly cl c0 c2).eval (iota r) = g.eval (iota r)) :
    r ∈ roundBad iota g cl c0 c2 := by
  by_contra h
  exact round_doom_persists iota g cl c0 c2 r hfalse h hmeet

/-- The reconstruction at 0 and 1: `s(0) = c0`, `s(1) = cl - c0`. So with a
false claim, `r = 0` is bad exactly when `c0 = g(0)` and `r = 1` exactly when
`cl - c0 = g(1)`; both are among the at most two roots counted. -/
theorem proverPoly_at_zero_one (cl c0 c2 : E) :
    (proverPoly cl c0 c2).eval 0 = c0 ∧ (proverPoly cl c0 c2).eval 1 = cl - c0 := by
  constructor <;> rw [proverPoly_eval] <;> ring

/-- The verifier's running claim after one round `(r, c0, c2)`. -/
def nextClaim (iota : K →+* E) (cl : E) (x : K × E × E) : E :=
  (proverPoly cl x.2.1 x.2.2).eval (iota x.1)

/-- The verifier's claim after all rounds. -/
def finalClaim (iota : K →+* E) : List (K × E × E) → E → E
  | [], cl => cl
  | x :: xs, cl => finalClaim iota xs (nextClaim iota cl x)

/-- Some round's challenge is in that round's bad set. Each round's bad set is
determined by the vectors folded at the earlier challenges, the running claim
and the round's own certificate entry: all fixed before its challenge. -/
def chainBad (iota : K →+* E) : List (K × E × E) → (ℕ → E) → (ℕ → E) → E → Prop
  | [], _, _, _ => False
  | x :: xs, f, u, cl =>
      x.1 ∈ roundBad iota (roundPoly (2 ^ xs.length) f u) cl x.2.1 x.2.2 ∨
      chainBad iota xs (fold (iota x.1) f) (fold (iota x.1) u) (nextClaim iota cl x)

/-- Round-by-round soundness of the sumcheck as the verifier runs it: if no
round's challenge is bad and the final check `C_n = f~(r) * u~(r)` passes, the
initial claim is the true sum. -/
theorem sumcheck_sound (iota : K →+* E) :
    ∀ (rounds : List (K × E × E)) (f u : ℕ → E) (cl : E),
      ¬ chainBad iota rounds f u cl →
      finalClaim iota rounds cl =
        foldAll iota (rounds.map Prod.fst) f 0 * foldAll iota (rounds.map Prod.fst) u 0 →
      cl = ∑ j ∈ range (2 ^ rounds.length), f j * u j
  | [], f, u, cl, _, hfin => by
    simpa [finalClaim, foldAll] using hfin
  | x :: xs, f, u, cl, hgood, hfin => by
    simp only [chainBad, not_or] at hgood
    have ih := sumcheck_sound iota xs (fold (iota x.1) f) (fold (iota x.1) u)
      (nextClaim iota cl x) hgood.2 (by simpa [finalClaim, foldAll] using hfin)
    rw [← roundPoly_eval] at ih
    rw [List.length_cons, pow_succ', ← roundPoly_sum]
    by_contra hne
    exact round_doom_persists iota _ cl x.2.1 x.2.2 x.1 (Ne.symm hne) hgood.1 ih

/-! ## D. The lambda row -/

/-- Bad combination challenges, a function of the two discrepancies
`a = S_W - claim` and `b = S_w - rhs2` only. -/
def lambdaBad (iota : K →+* E) (a b : E) : Finset K :=
  if a = 0 ∧ b = 0 then ∅ else Finset.univ.filter (fun l : K => a + iota l * b = 0)

theorem lambdaBad_card_le_one (iota : K →+* E) (a b : E) : (lambdaBad iota a b).card ≤ 1 := by
  unfold lambdaBad
  split_ifs with h
  · simp
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    by_cases hb : b = 0
    · exfalso
      apply h
      refine ⟨?_, hb⟩
      simpa [hb] using hx'
    · apply iota.injective
      have : (iota x - iota y) * b = 0 := by linear_combination hx' - hy'
      rcases mul_eq_zero.mp this with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hb

theorem lambda_sound (iota : K →+* E) (a b : E) (l : K) (hl : l ∉ lambdaBad iota a b)
    (h : a + iota l * b = 0) : a = 0 ∧ b = 0 := by
  by_contra hne
  apply hl
  unfold lambdaBad
  rw [if_neg hne, Finset.mem_filter]
  exact ⟨Finset.mem_univ l, h⟩

/-! ## E. The stage C residual pair (as in `TwoFamilyResidualBatch.lean`) -/

def residualPolynomial (r : Fin 22 → E) : E[X] :=
  ∑ i : Fin 22, Polynomial.monomial i.val (r i)

theorem residualPolynomial_coeff (r : Fin 22 → E) (i : Fin 22) :
    (residualPolynomial r).coeff i.val = r i := by
  classical
  rw [residualPolynomial]
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
theorem eval_residualPolynomial (iota : K →+* E) (rho : K) (r : Fin 22 → E) :
    (residualPolynomial r).eval (iota rho) = ∑ i : Fin 22, (iota rho) ^ i.val * r i := by
  classical
  simp [residualPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]

def rootsIn (iota : K →+* E) (r : Fin 22 → E) : Finset K :=
  Finset.univ.filter fun rho : K => (residualPolynomial r).eval (iota rho) = 0

def bad2 (iota : K →+* E) (r0 r1 : Fin 22 → E) : Finset K :=
  if residualPolynomial r0 ≠ 0 then rootsIn iota r0
    else if residualPolynomial r1 ≠ 0 then rootsIn iota r1
    else ∅

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

theorem all_zero_of_both_evals_zero_outside_bad2 (iota : K →+* E) (rho : K)
    (r0 r1 : Fin 22 → E) (hrho : rho ∉ bad2 iota r0 r1)
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

/-! ## F. Composition -/

/-- The query weight vector `w_j = sum_i rho^i B_{i,j}` (`B_{i,j}` = basis
value `j` at query `i`'s node). -/
def qweight (iota : K →+* E) (rho : K) (B : Fin 22 → ℕ → E) : ℕ → E :=
  fun j => ∑ i : Fin 22, (iota rho) ^ i.val * B i j

/-- `rhs2 = sum_i rho^i G_i` (`G_i` = second fold of query `i`). -/
def rhs2Of (iota : K →+* E) (rho : K) (G : Fin 22 → E) : E :=
  ∑ i : Fin 22, (iota rho) ^ i.val * G i

/-- The second-fold residuals `e_i - G_i`, `e_i = sum_j f_j B_{i,j}`. -/
def secondResidual (N : ℕ) (f : ℕ → E) (B : Fin 22 → ℕ → E) (G : Fin 22 → E) : Fin 22 → E :=
  fun i => (∑ j ∈ range N, f j * B i j) - G i

/-- `S_w - rhs2` is the batched second-fold residual. -/
theorem query_identity (iota : K →+* E) (rho : K) (N : ℕ) (f : ℕ → E)
    (B : Fin 22 → ℕ → E) (G : Fin 22 → E) :
    (∑ j ∈ range N, f j * qweight iota rho B j) - rhs2Of iota rho G =
      ∑ i : Fin 22, (iota rho) ^ i.val * secondResidual N f B G i := by
  unfold qweight rhs2Of secondResidual
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Composed statement for stages C and D, as the future verifier runs them.

Inputs (all model values): the final message `f`, the relation weight vector
`W`, the basis values `B` and second folds `G` of the 22 queries, the
first-fold residuals `r0` (`F_i - b_i`), the relation claim `claim`, the
challenges `rho`, `lam` and the rounds `(r_b, c0_b, c2_b)`.

Hypotheses: the stage C equality `sum_i rho^i r0_i = 0`; the final check
`C_n = f~(r) * (W~(r) + lam * w~(r))` with `C_0 = claim + lam * rhs2`; and no
bad event at `rho`, `lam` or any round.

Conclusion: every equality the pinned verifier checks at these positions
holds: `S_W = claim`, `S_w = rhs2`, all 22 first-fold residuals vanish and all
22 second-fold residuals vanish. -/
theorem stageCD_sound (iota : K →+* E) (rounds : List (K × E × E))
    (f W : ℕ → E) (B : Fin 22 → ℕ → E) (G : Fin 22 → E) (r0 : Fin 22 → E)
    (claim : E) (rho lam : K)
    (hC : ∑ i : Fin 22, (iota rho) ^ i.val * r0 i = 0)
    (hfinal : finalClaim iota rounds (claim + iota lam * rhs2Of iota rho G) =
      foldAll iota (rounds.map Prod.fst) f 0 *
        (foldAll iota (rounds.map Prod.fst) W 0 +
          iota lam * foldAll iota (rounds.map Prod.fst) (qweight iota rho B) 0))
    (hrho : rho ∉ bad2 iota r0 (secondResidual (2 ^ rounds.length) f B G))
    (hlam : lam ∉ lambdaBad iota
      ((∑ j ∈ range (2 ^ rounds.length), f j * W j) - claim)
      ((∑ j ∈ range (2 ^ rounds.length), f j * qweight iota rho B j) - rhs2Of iota rho G))
    (hrounds : ¬ chainBad iota rounds f (fun j => W j + iota lam * qweight iota rho B j)
      (claim + iota lam * rhs2Of iota rho G)) :
    (∑ j ∈ range (2 ^ rounds.length), f j * W j) = claim ∧
    (∑ j ∈ range (2 ^ rounds.length), f j * qweight iota rho B j) = rhs2Of iota rho G ∧
    (∀ i, r0 i = 0) ∧
    (∀ i, secondResidual (2 ^ rounds.length) f B G i = 0) := by
  set N := 2 ^ rounds.length with hN
  have hsum := sumcheck_sound iota rounds f (fun j => W j + iota lam * qweight iota rho B j)
    (claim + iota lam * rhs2Of iota rho G) hrounds
    (by rw [hfinal, foldAll_add_mul])
  have hcomb : ((∑ j ∈ range N, f j * W j) - claim) +
      iota lam * ((∑ j ∈ range N, f j * qweight iota rho B j) - rhs2Of iota rho G) = 0 := by
    have hsplit : ∑ j ∈ range N, f j * (W j + iota lam * qweight iota rho B j) =
        (∑ j ∈ range N, f j * W j) + iota lam * ∑ j ∈ range N, f j * qweight iota rho B j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit] at hsum
    linear_combination -hsum
  obtain ⟨hW, hw⟩ := lambda_sound iota _ _ lam hlam hcomb
  have h1 : ∑ i : Fin 22, (iota rho) ^ i.val * secondResidual N f B G i = 0 := by
    rw [← query_identity, hw]
  obtain ⟨z0, z1⟩ := all_zero_of_both_evals_zero_outside_bad2 iota rho r0 _ hrho hC h1
  exact ⟨sub_eq_zero.mp hW, sub_eq_zero.mp hw, z0, z1⟩

/-! ## G. Start-count arithmetic

`B = 15/2^109` is `PerAttemptEnvelope.B`. `atomUpper` is an upper bound on
`ceil(2^256/|K|)/2^256` with `|K| = (2^31-1)^4`, the per-element mass of the
`qm31_sample` decoder. -/

/-- The pinned common row envelope. -/
def envelopeB : ℚ := 15 / 2 ^ 109

/-- `|K| = (2^31 - 1)^4`. -/
def cardK : ℚ := (2 ^ 31 - 1) ^ 4

/-- Upper bound on the per-element decoder mass `ceil(2^256/|K|)/2^256`. -/
def atomUpper : ℚ := 1 / cardK + 1 / 2 ^ 256

theorem ceil_mass_le (M : ℕ) (hM : 0 < M) :
    ((⌈((2 : ℚ) ^ 256) / M⌉₊ : ℕ) : ℚ) / 2 ^ 256 ≤ 1 / (M : ℚ) + 1 / 2 ^ 256 := by
  have hc := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (2 : ℚ) ^ 256 / M by positivity)
  have hpos : (0 : ℚ) < 2 ^ 256 := by positivity
  rw [div_le_iff₀ hpos]
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  calc ((⌈((2 : ℚ) ^ 256) / M⌉₊ : ℕ) : ℚ) ≤ (2 : ℚ) ^ 256 / M + 1 := hc.le
    _ = (1 / (M : ℚ) + 1 / 2 ^ 256) * 2 ^ 256 := by field_simp

/-- Thirty-five starts already exceed `2^-100` under the uniform envelope:
any added sampler row breaks the zero-query criterion of the pinned bound if
every start is charged `B`. -/
theorem starts35_exceed : (1 : ℚ) / 2 ^ 100 < 35 * envelopeB := by
  unfold envelopeB
  norm_num

/-- The seven added rows plus the stage D reseed give 42 starts. -/
theorem starts42_value : 42 * envelopeB = 630 / 2 ^ 109 := by
  unfold envelopeB
  norm_num

/-- Each new row's cap is below the envelope: `2 * atomUpper ≤ B`. -/
theorem new_row_cap_le_B : 2 * atomUpper ≤ envelopeB := by
  unfold atomUpper cardK envelopeB
  norm_num

set_option exponentiation.threshold 600 in
/-- With a per-kind charge (the 34 pinned starts at `B`, the 8 new starts at
the round cap `2 * atomUpper`), the zero-query total stays below `2^-100`, with
the pinned collision, account, abort and query-scan terms unchanged. -/
theorem perKind_margin :
    34 * envelopeB + 8 * (2 * atomUpper) + 6 * (1161 ^ 2 + 2965 ^ 2) / 2 ^ 256 +
      1 / 2 ^ 126 + 1 / 2 ^ 454 < 1 / 2 ^ 100 := by
  unfold atomUpper cardK envelopeB
  norm_num

#print axioms sumcheck_sound
#print axioms roundBad_card_le_two
#print axioms roundBad_contains_every_coincidence
#print axioms proverPoly_at_zero_one
#print axioms lambdaBad_card_le_one
#print axioms lambda_sound
#print axioms bad2_card_le_21
#print axioms stageCD_sound
#print axioms foldAll_zero_eq_sum
#print axioms sum_eqw_bitProd
#print axioms query_weight_extension
#print axioms sum_eqw_digits3
#print axioms digit_weights
#print axioms sum_grouped
#print axioms sum_range_support
#print axioms starts35_exceed
#print axioms new_row_cap_le_B
#print axioms perKind_margin
#print axioms ceil_mass_le

end

end AspisFuture.StageD

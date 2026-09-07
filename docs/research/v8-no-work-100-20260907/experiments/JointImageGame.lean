import AspisFormal.V5FriConcreteEncoderApplicability
import Mathlib.Data.Finset.Powerset

/-! Research-only causal discrepancy game. No source, FS or arbitrary-oracle
coverage theorem. Every continuation may depend on every preceding challenge.
The only fixed polynomial at a root-bound step is the one sent BEFORE that
step's fresh challenge. All averaging is finite, exact and symbolic. -/
set_option autoImplicit false
namespace AspisV8.JointImageGame
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability
universe u
variable {K : Type u} [Field K] [DecidableEq K]

noncomputable def avg {A : Type*} (S : Finset A) (f : A → ℚ) : ℚ :=
  (∑ a ∈ S, f a) / S.card

theorem avg_le {A : Type*} (S : Finset A) (hs : S.Nonempty) (f : A → ℚ)
    (c : ℚ) (h : ∀ a ∈ S, f a ≤ c) : avg S f ≤ c := by
  have hc : (0 : ℚ) < S.card := by exact_mod_cast hs.card_pos
  apply (div_le_iff₀ hc).mpr
  calc ∑ a ∈ S, f a ≤ ∑ _a ∈ S, c := Finset.sum_le_sum h
       _ = c * S.card := by simp [mul_comm]

theorem avg_nonneg {A : Type*} (S : Finset A) (f : A → ℚ)
    (h : ∀ a ∈ S, 0 ≤ f a) : 0 ≤ avg S f :=
  div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

/-- An exceptional challenge is charged once, even when its continuation is
adaptive. The continuation bound is not assumed for exceptional outcomes. -/
theorem avg_exception {A : Type*} [DecidableEq A] (S B : Finset A)
    (hs : S.Nonempty) (hb : B ⊆ S) (f : A → ℚ) (e : ℚ) (he : 0 ≤ e)
    (hone : ∀ a ∈ S, f a ≤ 1) (hout : ∀ a ∈ S, a ∉ B → f a ≤ e) :
    avg S f ≤ (B.card : ℚ) / S.card + e := by
  have hc : (0 : ℚ) < S.card := by exact_mod_cast hs.card_pos
  have hh : ∑ a ∈ S, f a ≤ ∑ a ∈ S, ((if a ∈ B then 1 else 0 : ℚ) + e) := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hba : a ∈ B
    · simp only [if_pos hba]; linarith [hone a ha]
    · simpa only [if_neg hba, zero_add] using hout a ha hba
  have hi : ∑ a ∈ S, (if a ∈ B then 1 else 0 : ℚ) = B.card := by
    rw [← Finset.sum_filter]
    have hf : S.filter (fun a => a ∈ B) = B := by
      ext a
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun h => ⟨hb h, h⟩⟩
    rw [hf]; simp
  unfold avg
  apply (div_le_iff₀ hc).mpr
  rw [Finset.sum_add_distrib, hi] at hh
  have heq : ((B.card : ℚ) / S.card + e) * S.card = B.card + S.card * e := by
    field_simp
  rw [heq]
  simpa [nsmul_eq_mul] using hh

theorem root_count (S : Finset K) (p : K[X]) (hp : p ≠ 0)
    (d : ℕ) (hd : p.natDegree ≤ d) :
    (S.filter fun a => p.eval a = 0).card ≤ d := by
  apply (Polynomial.card_le_degree_of_subset_roots (p := p) ?_).trans hd
  intro a ha
  exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp ha).2

theorem avg_polynomial (S : Finset K) (hs : S.Nonempty) (p : K[X])
    (hp : p ≠ 0) (d : ℕ) (hd : p.natDegree ≤ d) (f : K → ℚ)
    (e : ℚ) (he : 0 ≤ e) (hone : ∀ a ∈ S, f a ≤ 1)
    (hout : ∀ a ∈ S, p.eval a ≠ 0 → f a ≤ e) :
    avg S f ≤ (d : ℚ)/S.card + e := by
  have h := avg_exception S (S.filter fun a => p.eval a = 0) hs
    (Finset.filter_subset _ _) f e he hone (by
      intro a ha hn
      apply hout a ha
      intro hz
      exact hn (Finset.mem_filter.mpr ⟨ha,hz⟩))
  have hc : ((S.filter fun a => p.eval a = 0).card : ℚ) ≤ d :=
    by exact_mod_cast root_count S p hp d hd
  exact h.trans (add_le_add (div_le_div_of_nonneg_right hc (Nat.cast_nonneg S.card)) (le_refl e))

/-- Boundary of the claimed-minus-honest degree-six relation polynomial. -/
def boundary (p : K[X]) : K := 4 * (p.coeff 0 + p.coeff 4)

theorem boundary_ne_zero (p : K[X]) (c : K) (h : boundary p = c) (hc : c ≠ 0) : p ≠ 0 := by
  intro hz; apply hc; rw [← h, hz]; simp [boundary]

/-- A causal relation strategy: the next polynomial can depend on the current
challenge. Boundary equality is algebraic, not an assumed acceptance bound. -/
inductive Rounds : ℕ → K → Type u
  | done (c : K) : Rounds 0 c
  | step {n : ℕ} {c : K} (p : K[X]) (degree : p.natDegree ≤ 6)
      (boundary_eq : boundary p = c)
      (next : (a : K) → Rounds n (p.eval a)) : Rounds (n+1) c

noncomputable def Rounds.prob (A : Finset K) : {n : ℕ} → {c : K} → Rounds n c → ℚ
  | _, c, .done _ => if c = 0 then 1 else 0
  | _, _, .step _ _ _ next => avg A (fun a => (next a).prob A)

theorem rounds_unit (A : Finset K) (ha : A.Nonempty) {n : ℕ} {c : K}
    (g : Rounds n c) : 0 ≤ g.prob A ∧ g.prob A ≤ 1 := by
  induction g with
  | done c => simp only [Rounds.prob]; split <;> norm_num
  | step p degree boundary_eq next ih =>
    exact ⟨avg_nonneg _ _ (fun a _ => (ih a).1), avg_le _ ha _ _ (fun a _ => (ih a).2)⟩

theorem rounds_false_bound (A : Finset K) (ha : A.Nonempty) {n : ℕ} {c : K}
    (g : Rounds n c) (hc : c ≠ 0) : g.prob A ≤ (n : ℚ)*6/A.card := by
  induction g with
  | done c => simp [Rounds.prob, hc]
  | @step n c p degree boundary_eq next ih =>
    have hn : (0 : ℚ) ≤ (n : ℚ)*6/A.card := by positivity
    have h := avg_polynomial A ha p (boundary_ne_zero p c boundary_eq hc) 6 degree
      (fun a => (next a).prob A) ((n : ℚ)*6/A.card) hn
      (fun a _ => (rounds_unit A ha (next a)).2) (fun a _ hz => ih a hz)
    change avg A (fun a => (next a).prob A) ≤ _
    convert h using 1 <;> push_cast <;> ring

noncomputable def imagePolynomial (prior e1 e2 : K) : K[X] :=
  monomialPolynomial ![prior, -e1, -e2]

theorem image_nonzero (prior e1 e2 : K) (h : e1 ≠ 0 ∨ e2 ≠ 0) :
    imagePolynomial prior e1 e2 ≠ 0 := by
  intro hz
  have hc1 := congrArg (fun p : K[X] => p.coeff 1) hz
  have hc2 := congrArg (fun p : K[X] => p.coeff 2) hz
  simp [imagePolynomial, monomialPolynomial, Fin.sum_univ_succ] at hc1 hc2
  exact h.elim (fun h => h hc1) (fun h => h hc2)

theorem image_degree (prior e1 e2 : K) : (imagePolynomial prior e1 e2).natDegree ≤ 2 :=
  monomialPolynomial_natDegree_le (by decide) _

noncomputable def shifted {q : ℕ} (prior : K) (r : Fin q → K) : K[X] :=
  C prior - X * monomialPolynomial r

theorem shifted_nonzero {q : ℕ} (prior : K) (r : Fin q → K)
    (h : prior ≠ 0 ∨ r ≠ 0) : shifted prior r ≠ 0 := by
  intro hz
  have heq : C prior = X * monomialPolynomial r := sub_eq_zero.mp hz
  have hp : prior = 0 := by
    have hc := congrArg (fun p : K[X] => p.coeff 0) heq
    simpa using hc
  have hr : r = 0 := by
    apply monomialPolynomial_injective
    have hm : monomialPolynomial r = 0 := by
      apply (mul_eq_zero.mp (show X * monomialPolynomial r = 0 by rw [← heq, hp]; simp)).resolve_left X_ne_zero
    simpa [monomialPolynomial] using hm
  exact h.elim (fun h => h hp) (fun h => h hr)

theorem shifted_degree {q : ℕ} (hq : 0 < q) (prior : K) (r : Fin q → K) :
    (shifted prior r).natDegree ≤ q := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_mul_le.trans
    have hd := monomialPolynomial_natDegree_le hq r
    simp only [Polynomial.natDegree_X]
    omega

theorem passing_schedules (D : Finset K) (p : K[X]) (hp : p ≠ 0)
    (d q : ℕ) (hd : p.natDegree ≤ d) :
    ((D.powersetCard q).filter (fun S => ∀ x ∈ S, p.eval x = 0)).card ≤ d.choose q := by
  have heq : (D.powersetCard q).filter (fun S => ∀ x ∈ S, p.eval x = 0) =
      (D.filter fun x => p.eval x = 0).powersetCard q := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hs,hq⟩,hz⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hs hx,hz x hx⟩,hq⟩
    · rintro ⟨hs,hq⟩
      exact ⟨⟨fun x hx => (Finset.mem_filter.mp (hs hx)).1,hq⟩,
        fun x hx => (Finset.mem_filter.mp (hs hx)).2⟩
  rw [heq, Finset.card_powersetCard]
  exact Nat.choose_le_choose q (root_count D p hp d hd)

/-- The actual final-minus-true-fold polynomial is chosen at this prefix,
AFTER alpha0 but BEFORE fresh queries. No recovered tuple or early target is
assumed. The two algebraic bridges are explicit: zero difference preserves the
prior discrepancy, and zero residual vector is precisely pointwise agreement.
They are not probability or successful-recovery premises. -/
structure AfterFold (D : Finset K) (q d : ℕ) (trueError : K) where
  difference : K[X]
  degree : difference.natDegree ≤ d
  prior : K
  same_prior : difference = 0 → prior = trueError
  residual : Finset K → Fin q → K
  zero_iff : ∀ S ∈ D.powersetCard q,
    residual S = 0 ↔ ∀ x ∈ S, difference.eval x = 0
  tail : (S : Finset K) → (rho : K) → Rounds 3 ((shifted prior (residual S)).eval rho)

noncomputable def AfterFold.prob {D : Finset K} {q d : ℕ} {e : K}
    (g : AfterFold D q d e) (A G : Finset K) : ℚ :=
  avg (D.powersetCard q) (fun S => avg G (fun rho => (g.tail S rho).prob A))

theorem after_unit {D : Finset K} {q d : ℕ} {e : K}
    (g : AfterFold D q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty) :
    0 ≤ g.prob A G ∧ g.prob A G ≤ 1 := by
  constructor
  · exact avg_nonneg _ _ (fun S _ => avg_nonneg _ _ (fun rho _ => (rounds_unit A ha (g.tail S rho)).1))
  · exact avg_le _ hs _ _ (fun S _ => avg_le _ hg _ _ (fun rho _ => (rounds_unit A ha (g.tail S rho)).2))

theorem after_false_bound {D : Finset K} {q d : ℕ} {e : K}
    (g : AfterFold D q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty) (hq : 0 < q) (he : e ≠ 0) :
    g.prob A G ≤ (d.choose q : ℚ)/(D.card.choose q) + (q : ℚ)/G.card + 18/A.card := by
  have tail_cap (S : Finset K) (hn : g.prior ≠ 0 ∨ g.residual S ≠ 0) :
      avg G (fun rho => (g.tail S rho).prob A) ≤ (q : ℚ)/G.card + 18/A.card := by
    apply avg_polynomial G hg (shifted g.prior (g.residual S))
      (shifted_nonzero _ _ hn) q (shifted_degree hq _ _) _ (18/A.card) (by positivity)
      (fun rho _ => (rounds_unit A ha (g.tail S rho)).2)
    intro rho _ hn
    convert rounds_false_bound A ha (g.tail S rho) hn using 1 <;> norm_num
  by_cases hz : g.difference = 0
  · have hp : g.prior ≠ 0 := by rw [g.same_prior hz]; exact he
    have h := avg_le _ hs _ _ (fun S _ => tail_cap S (Or.inl hp))
    change avg _ _ ≤ _
    have hn : (0 : ℚ) ≤ (d.choose q : ℚ)/(D.card.choose q) := by positivity
    linarith
  · let B := (D.powersetCard q).filter (fun S => ∀ x ∈ S, g.difference.eval x = 0)
    have hh := avg_exception (D.powersetCard q) B hs (Finset.filter_subset _ _)
      (fun S => avg G (fun rho => (g.tail S rho).prob A))
      ((q : ℚ)/G.card + 18/A.card) (by positivity)
      (fun S _ => avg_le _ hg _ _ (fun rho _ => (rounds_unit A ha (g.tail S rho)).2))
      (by
        intro S hS hn
        apply tail_cap S (Or.inr ?_)
        intro hr
        exact hn (Finset.mem_filter.mpr ⟨hS,(g.zero_iff S hS).mp hr⟩))
    have hb : (B.card : ℚ) ≤ d.choose q := by
      exact_mod_cast passing_schedules D g.difference hz d q g.degree
    have hd : (0 : ℚ) ≤ (D.card.choose q : ℚ) := by positivity
    rw [Finset.card_powersetCard] at hh
    have hc := div_le_div_of_nonneg_right hb hd
    change avg _ _ ≤ _
    linarith

/-- The first compact response can depend on tau; the adaptive final and
every subsequent response can depend on tau and alpha0. There is no provider
membership field. This models only an EXACT polynomial virtual quotient. -/
structure ImageGame (D : Finset K) (q d : ℕ) (prior e1 e2 : K) where
  first : K → K[X]
  degree : ∀ tau, (first tau).natDegree ≤ 6
  boundary_eq : ∀ tau, boundary (first tau) = (imagePolynomial prior e1 e2).eval tau
  after : (tau alpha : K) → AfterFold D q d ((first tau).eval alpha)

noncomputable def ImageGame.prob {D : Finset K} {q d : ℕ} {prior e1 e2 : K}
    (g : ImageGame D q d prior e1 e2) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => (g.after tau alpha).prob A G))

/-- Restricted ideal-game acceptance bound, derived by causal finite
averaging, root counts and the actual shifted batch. The 24/A term counts
all four relation repairs ONCE across the same/different-final partition. -/
theorem restricted_joint_bound {D : Finset K} {q d : ℕ} {prior e1 e2 : K}
    (g : ImageGame D q d prior e1 e2) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty)
    (hq : 0 < q) (hi : e1 ≠ 0 ∨ e2 ≠ 0) :
    g.prob A G ≤ ((q : ℚ)+2)/G.card + 24/A.card + (d.choose q : ℚ)/(D.card.choose q) := by
  let eps : ℚ := (d.choose q : ℚ)/(D.card.choose q) + (q : ℚ)/G.card + 18/A.card
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hfirst (tau : K) (ht : (imagePolynomial prior e1 e2).eval tau ≠ 0) :
      avg A (fun alpha => (g.after tau alpha).prob A G) ≤ 6/A.card + eps := by
    apply avg_polynomial A ha (g.first tau)
      (boundary_ne_zero _ _ (g.boundary_eq tau) ht) 6 (g.degree tau) _ eps heps
      (fun alpha _ => (after_unit (g.after tau alpha) A G ha hg hs).2)
    intro alpha _ hn
    exact after_false_bound (g.after tau alpha) A G ha hg hs hq hn
  have h := avg_polynomial G hg (imagePolynomial prior e1 e2)
    (image_nonzero prior e1 e2 hi) 2 (image_degree prior e1 e2)
    (fun tau => avg A (fun alpha => (g.after tau alpha).prob A G))
    (6/A.card+eps) (by positivity)
    (fun tau _ => avg_le A ha _ _ (fun alpha _ => (after_unit (g.after tau alpha) A G ha hg hs).2))
    (fun tau _ hn => hfirst tau hn)
  change avg _ _ ≤ _
  convert h using 1 <;> dsimp [eps] <;> ring

#print axioms rounds_false_bound
#print axioms image_nonzero
#print axioms image_degree
#print axioms shifted_nonzero
#print axioms shifted_degree
#print axioms avg_exception
#print axioms avg_polynomial
#print axioms passing_schedules
#print axioms after_false_bound
#print axioms restricted_joint_bound
end AspisV8.JointImageGame

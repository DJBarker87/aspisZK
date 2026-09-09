import RobustImageGame
import Mathlib.Data.Fintype.CardEmbedding

/-! Ordered distinct query schedules, not sorted representatives of query sets.
The scalar batch and adaptive continuation retain the first-occurrence order.
Counting is over embeddings Fin q into the fixed domain. This is the ideal
uniform ordered experiment; the bounded transcript sampler and FS lift are
separate obligations, not assumptions silently inferred from labels. -/
set_option autoImplicit false
namespace AspisV8.OrderedQueryGame
open Finset Polynomial
open AspisV8.JointImageGame AspisV8.RobustImageGame
variable {K : Type*} [Field K] [DecidableEq K]

abbrev Schedule (D : Finset K) (q : ℕ) := Fin q ↪ D

noncomputable def matching (D : Finset K) (q : ℕ) (P : K → Prop) [DecidablePred P] :
    Finset (Schedule D q) := univ.filter fun s => ∀ i, P (s i : K)

theorem schedule_card (D : Finset K) (q : ℕ) :
    Fintype.card (Schedule D q) = D.card.descFactorial q := by
  simp [Schedule]

noncomputable def filteredDomain (D : Finset K) (P : K → Prop) [DecidablePred P] :
    {x : D // P (x : K)} ≃ ↥(D.filter P) where
  toFun x := ⟨x.val.val, mem_filter.mpr ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val, (mem_filter.mp x.property).1⟩, (mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem matching_card (D : Finset K) (q : ℕ) (P : K → Prop) [DecidablePred P] :
    (matching D q P).card = (D.filter P).card.descFactorial q := by
  classical
  have he := Fintype.card_congr
    (Equiv.codRestrict (Fin q) {x : D | P (x : K)})
  have hc : Fintype.card {x : D // P (x : K)} = (D.filter P).card := by
    simpa using Fintype.card_congr (filteredDomain D P)
  rw [Fintype.card_embedding_eq, Fintype.card_fin] at he
  change Fintype.card {s : Schedule D q // ∀ i, P (s i : K)} =
    (Fintype.card {x : D // P (x : K)}).descFactorial q at he
  rw [hc] at he
  simpa [Fintype.card_subtype, matching] using he

theorem ordered_matching_ratio (D : Finset K) (q : ℕ)
    (P : K → Prop) [DecidablePred P] :
    ((matching D q P).card : ℚ) / Fintype.card (Schedule D q) =
      ((D.filter P).card.choose q : ℚ) / D.card.choose q := by
  rw [matching_card, schedule_card,
    Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  exact mul_div_mul_left _ _ (show (q.factorial : ℚ) ≠ 0 by
    exact_mod_cast Nat.factorial_ne_zero q)

theorem schedules_nonempty (D : Finset K) (q : ℕ) (hq : q ≤ D.card) :
    (univ : Finset (Schedule D q)).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_univ, schedule_card]
  exact Nat.descFactorial_pos.mpr hq

/-- Exactly the same geometric bound, now with the ordered query law and
without charging q! or assuming that the continuation is permutation invariant. -/
theorem ordered_noisy_ratio (D B : Finset K) (q d : ℕ) (noise : K → K)
    (hn : ∀ x ∈ D, x ∉ B → noise x = 0) (p : K[X])
    (hp : p ≠ 0) (hd : p.natDegree ≤ d) :
    ((matching D q (fun x => p.eval x = noise x)).card : ℚ) /
        Fintype.card (Schedule D q) ≤
      ((B.card+d).choose q : ℚ) / D.card.choose q := by
  rw [ordered_matching_ratio]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.choose_le_choose q (noisy_agreement_cap D B noise hn p hp d hd)

structure After (D B : Finset K) (q d : ℕ) (trueError : K) where
  difference : K[X]
  degree : difference.natDegree ≤ d
  noise : K → K
  noise_zero : ∀ x ∈ D, x ∉ B → noise x = 0
  prior : K
  same_prior : difference = 0 → prior = trueError
  residual : Schedule D q → Fin q → K
  zero_iff : ∀ s, residual s = 0 ↔
    ∀ i, difference.eval (s i : K) = noise (s i : K)
  tail : (s : Schedule D q) → (rho : K) →
    Rounds 3 ((shifted prior (residual s)).eval rho)

noncomputable def After.prob {D B : Finset K} {q d : ℕ} {e : K}
    (g : After D B q d e) (A G : Finset K) : ℚ :=
  avg univ (fun s => avg G (fun rho => (g.tail s rho).prob A))

theorem after_false_bound {D B : Finset K} {q d : ℕ} {e : K}
    (g : After D B q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hq : 0 < q) (hqD : q ≤ D.card) (he : e ≠ 0) :
    g.prob A G ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) +
      (q : ℚ)/G.card + 18/A.card := by
  classical
  have hs := schedules_nonempty D q hqD
  have tail_cap (s : Schedule D q) (hn : g.prior ≠ 0 ∨ g.residual s ≠ 0) :
      avg G (fun rho => (g.tail s rho).prob A) ≤ (q : ℚ)/G.card + 18/A.card := by
    apply avg_polynomial G hg (shifted g.prior (g.residual s))
      (shifted_nonzero _ _ hn) q (shifted_degree hq _ _) _ (18/A.card) (by positivity)
      (fun rho _ => (rounds_unit A ha (g.tail s rho)).2)
    intro rho _ hn
    convert rounds_false_bound A ha (g.tail s rho) hn using 1 <;> norm_num
  by_cases hz : g.difference = 0
  · have hp : g.prior ≠ 0 := by rw [g.same_prior hz]; exact he
    have h := avg_le _ hs _ _ (fun s _ => tail_cap s (Or.inl hp))
    change avg _ _ ≤ _
    have hn : (0 : ℚ) ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) := by positivity
    linarith
  · let E := matching D q (fun x => g.difference.eval x = g.noise x)
    have hh := avg_exception univ E hs (Finset.subset_univ _)
      (fun s => avg G (fun rho => (g.tail s rho).prob A))
      ((q : ℚ)/G.card + 18/A.card) (by positivity)
      (fun s _ => avg_le _ hg _ _ (fun rho _ => (rounds_unit A ha (g.tail s rho)).2))
      (by
        intro s _ hn
        apply tail_cap s (Or.inr ?_)
        intro hr
        exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (g.zero_iff s).mp hr⟩))
    have hb := ordered_noisy_ratio D B q d g.noise g.noise_zero
      g.difference hz g.degree
    rw [Finset.card_univ] at hh
    change avg _ _ ≤ _
    dsimp [E] at hh
    linarith

theorem after_off_final_bound {D B : Finset K} {q d : ℕ} {e : K}
    (g : After D B q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hq : 0 < q) (hqD : q ≤ D.card)
    (hne : g.difference ≠ 0) :
    g.prob A G ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) +
      (q : ℚ)/G.card + 18/A.card := by
  let h : After D B q d (1:K) := {
    difference := g.difference, degree := g.degree, noise := g.noise,
    noise_zero := g.noise_zero, prior := g.prior,
    same_prior := fun hz => False.elim (hne hz), residual := g.residual,
    zero_iff := g.zero_iff, tail := g.tail }
  exact after_false_bound h A G ha hg hq hqD one_ne_zero

#print axioms matching_card
#print axioms ordered_matching_ratio
#print axioms schedules_nonempty
#print axioms ordered_noisy_ratio
#print axioms after_false_bound
#print axioms after_off_final_bound
end AspisV8.OrderedQueryGame

import JointImageGame

/-! A new bounded-corruption extension, NOT exact polynomiality of the word.
An anchor is fixed before tau; the received word may be arbitrary on B fibres.
The old exact-image theorem and causal Rounds machinery are imported unchanged.
No semantic witness or global anchor-existence conclusion is assumed/proved. -/
set_option autoImplicit false
namespace AspisV8.RobustImageGame
open Polynomial Finset
open AspisV8.JointImageGame
variable {K : Type*} [Field K] [DecidableEq K]

/-- New geometric information: agreements with a different adaptive final
lie in the corrupt fibres OR roots of the polynomial difference. -/
theorem noisy_agreement_cap (D B : Finset K) (noise : K → K)
    (hn : ∀ x ∈ D, x ∉ B → noise x = 0) (p : K[X]) (hp : p ≠ 0)
    (d : ℕ) (hd : p.natDegree ≤ d) :
    (D.filter fun x => p.eval x = noise x).card ≤ B.card + d := by
  have sub : (D.filter fun x => p.eval x = noise x) ⊆
      B ∪ (D.filter fun x => p.eval x = 0) := by
    intro x hx
    obtain ⟨hxD, hx⟩ := Finset.mem_filter.mp hx
    by_cases hb : x ∈ B
    · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxD, by rw [hx, hn x hxD hb]⟩)
  exact (Finset.card_le_card sub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (root_count D p hp d hd) _))

theorem noisy_schedules_cap (D B : Finset K) (noise : K → K)
    (hn : ∀ x ∈ D, x ∉ B → noise x = 0) (p : K[X]) (hp : p ≠ 0)
    (d q : ℕ) (hd : p.natDegree ≤ d) :
    ((D.powersetCard q).filter (fun S => ∀ x ∈ S, p.eval x = noise x)).card ≤
      (B.card+d).choose q := by
  have heq : (D.powersetCard q).filter (fun S => ∀ x ∈ S, p.eval x = noise x) =
      (D.filter fun x => p.eval x = noise x).powersetCard q := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hs,hq⟩,hz⟩
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hs hx,hz x hx⟩,hq⟩
    · rintro ⟨hs,hq⟩
      exact ⟨⟨fun x hx => (Finset.mem_filter.mp (hs hx)).1,hq⟩,
        fun x hx => (Finset.mem_filter.mp (hs hx)).2⟩
  rw [heq, Finset.card_powersetCard]
  exact Nat.choose_le_choose q (noisy_agreement_cap D B noise hn p hp d hd)

/-- Source-shaped zero-vector interface, proved for actual evaluation
residuals and an enumeration whose range is the queried set. -/
theorem eval_residual_zero_iff {q : ℕ} (points : Fin q → K) (S : Finset K)
    (hs : ∀ x, x ∈ S ↔ ∃ i, points i = x) (f r : K → K) :
    (fun i => f (points i) - r (points i)) = 0 ↔ ∀ x ∈ S, f x = r x := by
  constructor
  · intro hz x hx
    obtain ⟨i,rfl⟩ := (hs x).mp hx
    exact sub_eq_zero.mp (congrFun hz i)
  · intro h
    funext i
    exact sub_eq_zero.mpr (h (points i) ((hs _).mpr ⟨i,rfl⟩))

/-- Both finals use the SAME carried weight. This identity is not an
existence-of-recovery premise. Query noise need not be zero. -/
theorem same_prior_dot {n : ℕ} (w v f : Fin n → K) (c : K) (hf : f = v) :
    c - (∑ i, w i * f i) = c - (∑ i, w i * v i) := by rw [hf]

structure NoisyAfter (D B : Finset K) (q d : ℕ) (trueError : K) where
  difference : K[X]
  degree : difference.natDegree ≤ d
  noise : K → K
  noise_zero : ∀ x ∈ D, x ∉ B → noise x = 0
  prior : K
  same_prior : difference = 0 → prior = trueError
  residual : Finset K → Fin q → K
  zero_iff : ∀ S ∈ D.powersetCard q,
    residual S = 0 ↔ ∀ x ∈ S, difference.eval x = noise x
  tail : (S : Finset K) → (rho : K) → Rounds 3 ((shifted prior (residual S)).eval rho)

noncomputable def NoisyAfter.prob {D B : Finset K} {q d : ℕ} {e : K}
    (g : NoisyAfter D B q d e) (A G : Finset K) : ℚ :=
  avg (D.powersetCard q) (fun S => avg G (fun rho => (g.tail S rho).prob A))

theorem noisy_unit {D B : Finset K} {q d : ℕ} {e : K}
    (g : NoisyAfter D B q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty) : g.prob A G ≤ 1 :=
  avg_le _ hs _ _ (fun S _ => avg_le _ hg _ _ (fun rho _ => (rounds_unit A ha (g.tail S rho)).2))

theorem noisy_false_bound {D B : Finset K} {q d : ℕ} {e : K}
    (g : NoisyAfter D B q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty) (hq : 0 < q) (he : e ≠ 0) :
    g.prob A G ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) + (q : ℚ)/G.card + 18/A.card := by
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
    have hn : (0 : ℚ) ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) := by positivity
    linarith
  · let E := (D.powersetCard q).filter (fun S => ∀ x ∈ S, g.difference.eval x = g.noise x)
    have hh := avg_exception (D.powersetCard q) E hs (Finset.filter_subset _ _)
      (fun S => avg G (fun rho => (g.tail S rho).prob A))
      ((q : ℚ)/G.card + 18/A.card) (by positivity)
      (fun S _ => avg_le _ hg _ _ (fun rho _ => (rounds_unit A ha (g.tail S rho)).2))
      (by
        intro S hS hn
        apply tail_cap S (Or.inr ?_)
        intro hr
        exact hn (Finset.mem_filter.mpr ⟨hS,(g.zero_iff S hS).mp hr⟩))
    have hb : (E.card : ℚ) ≤ (B.card+d).choose q := by
      exact_mod_cast noisy_schedules_cap D B g.noise g.noise_zero g.difference hz d q g.degree
    rw [Finset.card_powersetCard] at hh
    have hc := div_le_div_of_nonneg_right hb (show (0:ℚ) ≤ (D.card.choose q : ℚ) by positivity)
    change avg _ _ ≤ _
    linarith

structure NoisyGame (D B : Finset K) (q d : ℕ) (prior e1 e2 : K) where
  first : K → K[X]
  degree : ∀ tau, (first tau).natDegree ≤ 6
  boundary_eq : ∀ tau, boundary (first tau) = (imagePolynomial prior e1 e2).eval tau
  after : (tau alpha : K) → NoisyAfter D B q d ((first tau).eval alpha)

noncomputable def NoisyGame.prob {D B : Finset K} {q d : ℕ} {prior e1 e2 : K}
    (g : NoisyGame D B q d prior e1 e2) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => (g.after tau alpha).prob A G))

theorem image_nonzero_any (prior e1 e2 : K) (h : prior ≠ 0 ∨ e1 ≠ 0 ∨ e2 ≠ 0) :
    imagePolynomial prior e1 e2 ≠ 0 := by
  rcases h with hp | hi
  · intro hz
    have hc := congrArg (fun p : K[X] => p.coeff 0) hz
    apply hp
    simpa [imagePolynomial, AspisV5FriConcreteEncoderApplicability.monomialPolynomial,
      Fin.sum_univ_succ] using hc
  · exact image_nonzero prior e1 e2 hi

/-- Also covers an IMAGE-VALID anchor with a wrong ordinary relation claim.
The extra two-root allowance is conservative for that constant-error case. -/
theorem noisy_joint_bound {D B : Finset K} {q d : ℕ} {prior e1 e2 : K}
    (g : NoisyGame D B q d prior e1 e2) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty)
    (hq : 0 < q) (hi : prior ≠ 0 ∨ e1 ≠ 0 ∨ e2 ≠ 0) :
    g.prob A G ≤ ((q : ℚ)+2)/G.card + 24/A.card + ((B.card+d).choose q : ℚ)/(D.card.choose q) := by
  let eps : ℚ := ((B.card+d).choose q : ℚ)/(D.card.choose q) + (q : ℚ)/G.card + 18/A.card
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hfirst (tau : K) (ht : (imagePolynomial prior e1 e2).eval tau ≠ 0) :
      avg A (fun alpha => (g.after tau alpha).prob A G) ≤ 6/A.card + eps := by
    apply avg_polynomial A ha (g.first tau)
      (boundary_ne_zero _ _ (g.boundary_eq tau) ht) 6 (g.degree tau) _ eps heps
      (fun alpha _ => noisy_unit (g.after tau alpha) A G ha hg hs)
    intro alpha _ hn
    exact noisy_false_bound (g.after tau alpha) A G ha hg hs hq hn
  have h := avg_polynomial G hg (imagePolynomial prior e1 e2)
    (image_nonzero_any prior e1 e2 hi) 2 (image_degree prior e1 e2)
    (fun tau => avg A (fun alpha => (g.after tau alpha).prob A G))
    (6/A.card+eps) (by positivity)
    (fun tau _ => avg_le A ha _ _ (fun alpha _ => noisy_unit (g.after tau alpha) A G ha hg hs))
    (fun tau _ hn => hfirst tau hn)
  change avg _ _ ≤ _
  convert h using 1 <;> dsimp [eps] <;> ring

/-- New reduction even when the anchor's image AND ordinary claim are valid:
an accepted DIFFERENT final has this small probability at each query prefix.
Only the equal-final branch remains for semantic/component extraction. -/
theorem noisy_off_final_bound {D B : Finset K} {q d : ℕ} {e : K}
    (g : NoisyAfter D B q d e) (A G : Finset K) (ha : A.Nonempty)
    (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty) (hq : 0 < q)
    (hne : g.difference ≠ 0) :
    g.prob A G ≤ ((B.card+d).choose q : ℚ)/(D.card.choose q) + (q : ℚ)/G.card + 18/A.card := by
  -- On different-final branches the same_prior implication is vacuous;
  -- reindexing does not alter prior, residuals, tail, or acceptance.
  let h : NoisyAfter D B q d (1:K) := {
    difference := g.difference, degree := g.degree, noise := g.noise,
    noise_zero := g.noise_zero, prior := g.prior,
    same_prior := fun hz => False.elim (hne hz), residual := g.residual,
    zero_iff := g.zero_iff, tail := g.tail }
  exact noisy_false_bound h A G ha hg hs hq one_ne_zero

#print axioms noisy_agreement_cap
#print axioms noisy_schedules_cap
#print axioms eval_residual_zero_iff
#print axioms same_prior_dot
#print axioms noisy_false_bound
#print axioms noisy_joint_bound
#print axioms noisy_off_final_bound
end AspisV8.RobustImageGame

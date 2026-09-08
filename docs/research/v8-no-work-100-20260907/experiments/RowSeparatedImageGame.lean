import RobustImageGame

/-! Research-only repair of the constant-coefficient collision. This file
does NOT assume the inactive claim exact. The four error coefficients must be
fixed before kappa; they can depend on gamma and all earlier messages. A
pre-kappa anchor may have a non-polynomial word within B corrupt fibres.
Per-lane recovery, source translation, privacy and FS remain separate. -/
set_option autoImplicit false
namespace AspisV8.RowSeparatedImageGame
open Polynomial Finset
open AspisV8.JointImageGame AspisV8.RobustImageGame
variable {K : Type*} [Field K] [DecidableEq K]

theorem unshifted_cancel (delta kappa : K) :
    -delta + delta + kappa*0 + kappa^2*0 = 0 := by ring

theorem shifted_cancel (delta kappa : K) :
    -delta + kappa*delta + kappa^2*0 + kappa^3*0 = (kappa-1)*delta := by ring

theorem shifted_cancel_iff (delta kappa : K) (hd : delta ≠ 0) :
    -delta + kappa*delta + kappa^2*0 + kappa^3*0 = 0 ↔ kappa = 1 := by
  rw [shifted_cancel, mul_eq_zero, or_iff_left hd, sub_eq_zero]

noncomputable def rowPolynomial (inactiveError : K) (pointError : Fin 3 → K) : K[X] :=
  shifted inactiveError (fun j => -pointError j)

theorem rowPolynomial_eval (i : K) (e : Fin 3 → K) (k : K) :
    (rowPolynomial i e).eval k = i + k*e 0 + k^2*e 1 + k^3*e 2 := by
  simp [rowPolynomial, shifted,
    AspisV5FriConcreteEncoderApplicability.monomialPolynomial, Fin.sum_univ_succ]
  ring

theorem rowPolynomial_nonzero (i : K) (e : Fin 3 → K) (h : i ≠ 0 ∨ e ≠ 0) :
    rowPolynomial i e ≠ 0 := by
  apply shifted_nonzero
  rcases h with hi | he
  · exact Or.inl hi
  · right
    intro hz
    apply he
    funext j
    have h := congrFun hz j
    simpa using h

theorem rowPolynomial_degree (i : K) (e : Fin 3 → K) :
    (rowPolynomial i e).natDegree ≤ 3 := shifted_degree (by decide) _ _

theorem row_root_cap (G : Finset K) (i : K) (e : Fin 3 → K)
    (h : i ≠ 0 ∨ e ≠ 0) :
    (G.filter fun k => (rowPolynomial i e).eval k = 0).card ≤ 3 :=
  root_count G _ (rowPolynomial_nonzero i e h) 3 (rowPolynomial_degree i e)

/-- With a valid anchor image, tau changes responses but cannot cancel the
constant wrong ordinary discrepancy. Avoid charging a spurious two tau roots. -/
theorem valid_image_wrong_ordinary {D B : Finset K} {q d : ℕ} {e : K}
    (g : NoisyGame D B q d e 0 0) (A G : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hs : (D.powersetCard q).Nonempty)
    (hq : 0 < q) (he : e ≠ 0) :
    g.prob A G ≤ (q:ℚ)/G.card + 24/A.card + ((B.card+d).choose q:ℚ)/(D.card.choose q) := by
  let eps : ℚ := ((B.card+d).choose q:ℚ)/(D.card.choose q) + (q:ℚ)/G.card + 18/A.card
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hb (tau : K) : boundary (g.first tau) = e := by
    simpa [imagePolynomial, AspisV5FriConcreteEncoderApplicability.monomialPolynomial,
      Fin.sum_univ_succ] using g.boundary_eq tau
  have ht (tau : K) : avg A (fun a => (g.after tau a).prob A G) ≤ 6/A.card+eps := by
    apply avg_polynomial A ha (g.first tau) (boundary_ne_zero _ e (hb tau) he)
      6 (g.degree tau) _ eps heps
      (fun a _ => noisy_unit (g.after tau a) A G ha hg hs)
    intro a _ hn
    exact noisy_false_bound (g.after tau a) A G ha hg hs hq hn
  have h := avg_le G hg _ _ (fun tau _ => ht tau)
  change avg G _ ≤ _
  convert h using 1 <;> dsimp [eps] <;> ring

/-- Joint causal bound after the repair, not merely another polynomial root
count. All later strategies can depend on kappa. No inactiveExact premise. -/
theorem row_separated_joint_bound {D B : Finset K} {q d : ℕ}
    (i : K) (e : Fin 3 → K) (bad : i ≠ 0 ∨ e ≠ 0)
    (strategy : (k : K) → NoisyGame D B q d ((rowPolynomial i e).eval k) 0 0)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hs : (D.powersetCard q).Nonempty) (hq : 0 < q) :
    avg G (fun k => (strategy k).prob A G) ≤
      ((q:ℚ)+3)/G.card + 24/A.card + ((B.card+d).choose q:ℚ)/(D.card.choose q) := by
  let eps : ℚ := (q:ℚ)/G.card + 24/A.card + ((B.card+d).choose q:ℚ)/(D.card.choose q)
  have h := avg_polynomial G hg (rowPolynomial i e) (rowPolynomial_nonzero i e bad)
    3 (rowPolynomial_degree i e) (fun k => (strategy k).prob A G) eps
    (by dsimp [eps]; positivity)
    (by
      intro k _
      exact avg_le G hg _ _ (fun tau _ => avg_le A ha _ _
        (fun a _ => noisy_unit ((strategy k).after tau a) A G ha hg hs)))
    (fun k _ hn => valid_image_wrong_ordinary (strategy k) A G ha hg hs hq hn)
  convert h using 1 <;> dsimp [eps] <;> ring

#print axioms unshifted_cancel
#print axioms shifted_cancel_iff
#print axioms rowPolynomial_eval
#print axioms rowPolynomial_nonzero
#print axioms row_root_cap
#print axioms valid_image_wrong_ordinary
#print axioms row_separated_joint_bound
end AspisV8.RowSeparatedImageGame

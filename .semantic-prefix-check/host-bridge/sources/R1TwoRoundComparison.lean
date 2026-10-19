import R1FunctionalBatchClean

/-! Two sequential polynomial comparisons over one fixed candidate family.

This is the deterministic comparison and root-counting component. It does
not assert extraction of a candidate, the concrete round boundary identities,
prefix causality, sampler laws, or a Fiat--Shamir reduction. Those must be
instantiated separately. In particular, the first family must be fixed
before alpha0, and the second before alpha1. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.TwoRoundComparison
open Polynomial

variable {K T : Type*} [Field K] [Fintype K] [DecidableEq K]

def comparisonBad (ts : Finset T) (claimed : K[X])
    (truth : T → K[X]) : Finset K :=
  functionalBadRoots ts (fun t => claimed - truth t)

theorem comparison_bad_card_le_600
    (ts : Finset T) (claimed : K[X]) (truth : T → K[X])
    (hlist : ts.card ≤ 100) (hp : claimed.natDegree ≤ 6)
    (ht : ∀ t ∈ ts, (truth t).natDegree ≤ 6) :
    (comparisonBad ts claimed truth).card ≤ 600 := by
  apply functional_bad_roots_card_le_600 ts _ hlist
  intro t hmem
  exact (natDegree_sub_le _ _).trans (max_le hp (ht t hmem))

theorem comparison_eq_of_eval_eq
    (ts : Finset T) (claimed : K[X]) (truth : T → K[X])
    (alpha : K) (hgood : alpha ∉ comparisonBad ts claimed truth)
    (t : T) (ht : t ∈ ts)
    (heval : claimed.eval alpha = (truth t).eval alpha) :
    claimed = truth t := by
  apply sub_eq_zero.mp
  apply eval_zero_outside_functional_bad_roots ts
    (fun t => claimed - truth t) alpha hgood t ht
  simpa only [eval_sub, sub_eq_zero] using heval

def boundary (p : K[X]) : K := p.coeff 0 + p.coeff 4

/-- Final evaluation agreement identifies round one; its boundary then
identifies round zero. Both comparisons use the same extracted candidate. -/
theorem two_round_comparison
    (ts : Finset T) (p0 p1 : K[X])
    (r0 : T → K[X]) (r1 : K → T → K[X])
    (alpha0 alpha1 scale : K) (hscale : scale ≠ 0)
    (hgood0 : alpha0 ∉ comparisonBad ts p0 r0)
    (hgood1 : alpha1 ∉ comparisonBad ts p1 (r1 alpha0))
    (t : T) (ht : t ∈ ts)
    (hfinal : p1.eval alpha1 = (r1 alpha0 t).eval alpha1)
    (hboundary : boundary p1 = scale * p0.eval alpha0)
    (htrue : boundary (r1 alpha0 t) = scale * (r0 t).eval alpha0) :
    p0 = r0 t ∧ p1 = r1 alpha0 t := by
  have h1 : p1 = r1 alpha0 t :=
    comparison_eq_of_eval_eq ts p1 (r1 alpha0) alpha1 hgood1 t ht hfinal
  have heval0 : p0.eval alpha0 = (r0 t).eval alpha0 := by
    apply mul_left_cancel₀ hscale
    calc
      scale * p0.eval alpha0 = boundary p1 := hboundary.symm
      _ = boundary (r1 alpha0 t) := congrArg boundary h1
      _ = scale * (r0 t).eval alpha0 := htrue
  exact ⟨comparison_eq_of_eval_eq ts p0 r0 alpha0 hgood0 t ht heval0, h1⟩

/-- The initial boundary recovers the unscaled claim after comparison. -/
theorem claim_eq_of_compared_boundary
    (p truth : K[X]) (claim pairing scale : K) (hscale : scale ≠ 0)
    (hsame : p = truth)
    (haccepted : boundary p = scale * claim)
    (htrue : boundary truth = scale * pairing) :
    claim = pairing := by
  apply mul_left_cancel₀ hscale
  calc
    scale * claim = boundary p := haccepted.symm
    _ = boundary truth := congrArg boundary hsame
    _ = scale * pairing := htrue

#print axioms comparison_bad_card_le_600
#print axioms comparison_eq_of_eval_eq
#print axioms two_round_comparison
#print axioms claim_eq_of_compared_boundary
end AspisR1.TwoRoundComparison
end

import R1RoundPairing
import R1TwoRoundComparison

/-! Exact deterministic composition of the generic radix-four pairing and the
two-round polynomial comparison lemma.  This module adds no extraction,
causality, source-semantics, sampler, or security premise. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.TwoRoundPairing

open Polynomial

variable {K T : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]

def round0Truth {n : Nat} (q : T → Fin (4 * (4 * n)) → K)
    (w : Fin (4 * (4 * n)) → K) : T → K[X] :=
  fun t => AspisR1.RoundPairing.roundPolynomial (q t) w

def round1Truth {n : Nat} (alpha : K)
    (q : T → Fin (4 * (4 * n)) → K)
    (w : Fin (4 * (4 * n)) → K) : T → K[X] :=
  fun t => AspisR1.RoundPairing.roundPolynomial
    (AspisR1.RoundPairing.primalFold alpha (q t))
    (AspisR1.RoundPairing.dualFold alpha w)

theorem round0_bad_card_le_600 {n : Nat}
    (ts : Finset T) (claimed : K[X])
    (q : T → Fin (4 * (4 * n)) → K)
    (w : Fin (4 * (4 * n)) → K)
    (hlist : ts.card ≤ 100) (hclaimed : claimed.natDegree ≤ 6) :
    (AspisR1.TwoRoundComparison.comparisonBad ts claimed
      (round0Truth q w)).card ≤ 600 := by
  apply AspisR1.TwoRoundComparison.comparison_bad_card_le_600
    ts claimed (round0Truth q w) hlist hclaimed
  intro t _ht
  exact AspisR1.RoundPairing.round_degree (q t) w

theorem round1_bad_card_le_600 {n : Nat}
    (ts : Finset T) (claimed : K[X]) (alpha : K)
    (q : T → Fin (4 * (4 * n)) → K)
    (w : Fin (4 * (4 * n)) → K)
    (hlist : ts.card ≤ 100) (hclaimed : claimed.natDegree ≤ 6) :
    (AspisR1.TwoRoundComparison.comparisonBad ts claimed
      (round1Truth alpha q w)).card ≤ 600 := by
  apply AspisR1.TwoRoundComparison.comparison_bad_card_le_600
    ts claimed (round1Truth alpha q w) hlist hclaimed
  intro t _ht
  exact AspisR1.RoundPairing.round_degree
    (AspisR1.RoundPairing.primalFold alpha (q t))
    (AspisR1.RoundPairing.dualFold alpha w)

/-- If both polynomial comparisons pass and the final vector is extracted by
the two specified folds, then the accepted round polynomials and initial dot
product are uniquely determined.  The two true boundary identities and final
evaluation identity are derived from `round_boundary` and `round_eval`. -/
theorem two_round_pairing
    {n : Nat} (h4 : (4 : K) ≠ 0)
    (ts : Finset T) (q : T → Fin (4 * (4 * n)) → K)
    (w : Fin (4 * (4 * n)) → K) (t : T) (ht : t ∈ ts)
    (p0 p1 : K[X]) (alpha0 alpha1 claim : K)
    (f : Fin n → K)
    (hgood0 : alpha0 ∉ AspisR1.TwoRoundComparison.comparisonBad
      ts p0 (round0Truth q w))
    (hgood1 : alpha1 ∉ AspisR1.TwoRoundComparison.comparisonBad
      ts p1 (round1Truth alpha0 q w))
    (hextract : f = AspisR1.RoundPairing.primalFold alpha1
      (AspisR1.RoundPairing.primalFold alpha0 (q t)))
    (hfinal : p1.eval alpha1 = AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold alpha1
        (AspisR1.RoundPairing.dualFold alpha0 w)))
    (haccepted1 : AspisR1.TwoRoundComparison.boundary p1 =
      AspisR1.RoundPairing.quarter * p0.eval alpha0)
    (haccepted0 : AspisR1.TwoRoundComparison.boundary p0 =
      AspisR1.RoundPairing.quarter * claim) :
    p0 = round0Truth q w t ∧
      p1 = round1Truth alpha0 q w t ∧
      claim = AspisR1.RoundPairing.dot (q t) w := by
  have hquarter : (AspisR1.RoundPairing.quarter (K := K) : K) ≠ (0 : K) := by
    change ((4 : K)⁻¹) ≠ 0
    exact inv_ne_zero h4
  have hfinal_eval : p1.eval alpha1 =
      (round1Truth alpha0 q w t).eval alpha1 := by
    calc
      p1.eval alpha1 = AspisR1.RoundPairing.dot f
          (AspisR1.RoundPairing.dualFold alpha1
            (AspisR1.RoundPairing.dualFold alpha0 w)) := hfinal
      _ = AspisR1.RoundPairing.dot
          (AspisR1.RoundPairing.primalFold alpha1
            (AspisR1.RoundPairing.primalFold alpha0 (q t)))
          (AspisR1.RoundPairing.dualFold alpha1
            (AspisR1.RoundPairing.dualFold alpha0 w)) := by rw [hextract]
      _ = (round1Truth alpha0 q w t).eval alpha1 := by
        symm
        exact AspisR1.RoundPairing.round_eval alpha1
          (AspisR1.RoundPairing.primalFold alpha0 (q t))
          (AspisR1.RoundPairing.dualFold alpha0 w)
  have htrue1 :
      AspisR1.TwoRoundComparison.boundary (round1Truth alpha0 q w t) =
        AspisR1.RoundPairing.quarter * (round0Truth q w t).eval alpha0 := by
    calc
      AspisR1.TwoRoundComparison.boundary (round1Truth alpha0 q w t) =
          AspisR1.RoundPairing.quarter *
            AspisR1.RoundPairing.dot
              (AspisR1.RoundPairing.primalFold alpha0 (q t))
              (AspisR1.RoundPairing.dualFold alpha0 w) := by
        change (AspisR1.RoundPairing.roundPolynomial
            (AspisR1.RoundPairing.primalFold alpha0 (q t))
            (AspisR1.RoundPairing.dualFold alpha0 w)).coeff 0 +
          (AspisR1.RoundPairing.roundPolynomial
            (AspisR1.RoundPairing.primalFold alpha0 (q t))
            (AspisR1.RoundPairing.dualFold alpha0 w)).coeff 4 = _
        exact AspisR1.RoundPairing.round_boundary
          (AspisR1.RoundPairing.primalFold alpha0 (q t))
          (AspisR1.RoundPairing.dualFold alpha0 w)
      _ = AspisR1.RoundPairing.quarter *
          (round0Truth q w t).eval alpha0 := by
        unfold round0Truth
        exact congrArg (fun z : K => AspisR1.RoundPairing.quarter * z)
          (AspisR1.RoundPairing.round_eval alpha0 (q t) w).symm
  have hcomp := AspisR1.TwoRoundComparison.two_round_comparison
    ts p0 p1 (round0Truth q w) (fun a => round1Truth a q w)
    alpha0 alpha1 AspisR1.RoundPairing.quarter hquarter
    hgood0 hgood1 t ht hfinal_eval haccepted1 htrue1
  have htrue0 : AspisR1.TwoRoundComparison.boundary
      (round0Truth q w t) = AspisR1.RoundPairing.quarter *
        AspisR1.RoundPairing.dot (q t) w := by
    change (AspisR1.RoundPairing.roundPolynomial (q t) w).coeff 0 +
      (AspisR1.RoundPairing.roundPolynomial (q t) w).coeff 4 = _
    exact AspisR1.RoundPairing.round_boundary (q t) w
  have hclaim : claim = AspisR1.RoundPairing.dot (q t) w := by
    apply mul_left_cancel₀ hquarter
    calc
      AspisR1.RoundPairing.quarter * claim =
          AspisR1.TwoRoundComparison.boundary p0 := haccepted0.symm
      _ = AspisR1.TwoRoundComparison.boundary (round0Truth q w t) :=
        congrArg AspisR1.TwoRoundComparison.boundary hcomp.1
      _ = AspisR1.RoundPairing.quarter *
          AspisR1.RoundPairing.dot (q t) w := htrue0
  exact ⟨hcomp.1, ⟨hcomp.2, hclaim⟩⟩

#print axioms round0_bad_card_le_600
#print axioms round1_bad_card_le_600
#print axioms two_round_pairing

end AspisR1.TwoRoundPairing
end

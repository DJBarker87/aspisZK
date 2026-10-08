import R0P.SemClosed
import R0P.SemBadSets

/-!
G13 stop evidence for the fixed semantic-round coverage obligation.

`Zerocheck.lean:88–89` existentially quantifies a fresh polynomial after the
challenge vector has been supplied. It therefore holds for every vector,
as witnessed below by `X - C (α i)`. `SemClosed.lean:33,62` requires its
negation; avoiding the prefix-fixed strategy/honest difference polynomials
cannot supply that premise. `SemBadSets.badAlphaStrategy` is a different,
strategy-specific event (SemBadSets.lean:929–931,991–996,1147–1154).

No semantic-round classifier, round-cardinality theorem, coverage theorem,
or soundness wrapper is claimed. The existing interfaces remain unchanged.
-/

set_option autoImplicit false

namespace R0P
open Polynomial
open R0P.Sumcheck

variable {K : Type} [Field K]

/-- Every nonempty challenge vector satisfies the current existential
bad-round event whenever the degree bound is at least one. -/
theorem badAlpha_all_rounds {n d : Nat} (hn : 0 < n) (hd : 1 ≤ d)
    (α : Fin n → K) : BadAlpha d n α := by
  let i : Fin n := ⟨0, hn⟩
  let p : K[X] := X - C (α i)
  have hcoeff : p.coeff 1 = 1 := by simp [p]
  have hp : p ≠ 0 := by
    intro h
    have hc := congrArg (fun q : K[X] => q.coeff 1) h
    rw [hcoeff] at hc
    exact one_ne_zero hc
  have hdeg : p.natDegree ≤ 1 := by
    dsimp [p]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (by simp) (by simp))
  have heval : p.eval (α i) = 0 := by simp [p]
  exact ⟨i, p, hp, hdeg.trans hd, heval⟩

#print axioms badAlpha_all_rounds

theorem badAlpha_27_10 (α : Fin 10 → K) : BadAlpha 27 10 α :=
  badAlpha_all_rounds (by decide) (by decide) α

#print axioms badAlpha_27_10

theorem badAlpha_27_10_negation_impossible (α : Fin 10 → K)
    (hα : ¬ BadAlpha 27 10 α) : False :=
  hα (badAlpha_27_10 α)

#print axioms badAlpha_27_10_negation_impossible

/-- When the prover's round polynomials equal the honest ones, none of their
differences is a nonzero root polynomial; the current `BadAlpha` still holds. -/
theorem equal_round_polynomials_do_not_exclude_badAlpha (α : Fin 10 → K)
    (honest : Fin 10 → K[X]) :
    (∀ i : Fin 10, ¬ (honest i - honest i ≠ 0 ∧
      (honest i - honest i).eval (α i) = 0)) ∧ BadAlpha 27 10 α := by
  refine ⟨?_, badAlpha_27_10 α⟩
  intro i h
  exact h.1 (sub_self _)

#print axioms equal_round_polynomials_do_not_exclude_badAlpha

end R0P

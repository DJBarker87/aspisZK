import SameBodyQueryClaimExact
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# S4 compact evaluation bridge

This is an algebra-only bridge for the concrete `ringArithmetic` callback.
It does not construct a selected-source execution, identify a submitted wire
with `sent`, or establish acceptance.  Its purpose is to prevent the ordinary
event from treating `Arithmetic.evaluate7` as an unconstrained callback.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000

namespace AspisV8Completion.FSV8S4CompactEvaluationBridge

open Polynomial
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R]
local instance : DecidableEq R := Classical.decEq R

/-- The exact reverse/foldl operation used by `ringArithmetic`. -/
def sourceHorner7 (p : Fin 7 → R) (x : R) : R :=
  (List.ofFn p).reverse.foldl (fun c a => c * x + a) 0

theorem sourceHorner7_expanded (p : Fin 7 → R) (x : R) :
    sourceHorner7 p x =
      p 0 + p 1*x + p 2*x^2 + p 3*x^3 + p 4*x^4 + p 5*x^5 + p 6*x^6 := by
  simp [sourceHorner7, List.ofFn_succ, List.reverse_cons,
    List.foldl_cons, List.foldl_nil] <;> ring

theorem sourceHorner7_eq_sum (p : Fin 7 → R) (x : R) :
    sourceHorner7 p x = ∑ i : Fin 7, p i * x ^ i.val := by
  rw [sourceHorner7_expanded]
  simp [Fin.sum_univ_succ]
  <;> ring

theorem sourceHorner7_eq_polynomial_eval (p : Fin 7 → R) (x : R) :
    sourceHorner7 p x = (Polynomial.ofFn 7 p).eval x := by
  classical
  rw [sourceHorner7_eq_sum, Polynomial.ofFn_eq_sum_monomial]
  rw [Polynomial.eval_finsetSum]
  simp

/-- This closes the specific `evaluate7` API seam for the concrete callback. -/
theorem actual_evaluate7_eq_ofFn_eval (quarter : R) (p : Fin 7 → R) (x : R) :
    (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic.evaluate7 p x =
      (Polynomial.ofFn 7 p).eval x := by
  exact sourceHorner7_eq_polynomial_eval p x

/-- The compact polynomial consumed by the concrete initial relation round. -/
def actualCompactPolynomial (quarter claim : R) (sent : SameBodyRelation.Sent R) : R[X] :=
  Polynomial.ofFn 7
    (SameBodyRelation.compact
      (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent)

theorem actual_compact_evaluation (quarter claim : R)
    (sent : SameBodyRelation.Sent R) (alpha : R) :
    (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic.evaluate7
        (SameBodyRelation.compact
          (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) alpha =
      (actualCompactPolynomial quarter claim sent).eval alpha :=
  actual_evaluate7_eq_ofFn_eval quarter _ alpha

theorem actual_compact_degree (quarter claim : R) (sent : SameBodyRelation.Sent R) :
    (actualCompactPolynomial quarter claim sent).natDegree ≤ 6 := by
  classical
  have h := Polynomial.ofFn_natDegree_lt (by decide : 1 ≤ 7)
    (SameBodyRelation.compact
      (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent)
  change (actualCompactPolynomial quarter claim sent).natDegree < 7 at h
  omega

theorem actual_compact_boundary (quarter claim : R) (sent : SameBodyRelation.Sent R)
    (quarterChecked : (4 : R) * quarter = 1) :
    4 * ((SameBodyRelation.compact
        (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) 0 +
      (SameBodyRelation.compact
        (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) 4) = claim := by
  change (4 : R) * (sent 0 + (claim * quarter - sent 0)) = claim
  calc
    4 * (sent 0 + (claim * quarter - sent 0)) = claim * (4 * quarter) := by ring
    _ = claim := by rw [quarterChecked, mul_one]

/-- A source evaluation mismatch is the literal polynomial discrepancy. -/
theorem source_discrepancy_eval (quarter claim alpha : R)
    (sent : SameBodyRelation.Sent R) (honest : R[X]) :
    (actualCompactPolynomial quarter claim sent - honest).eval alpha =
      (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic.evaluate7
        (SameBodyRelation.compact
          (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) alpha
        - honest.eval alpha := by
  rw [Polynomial.eval_sub, actual_compact_evaluation]

/-! ## Finite prechallenge candidate families

The definitions below deliberately consume a *supplied finite family*.  They
are the algebraic ordinary-event consumer; constructing that family from the
selected source and proving that it is fixed before `alpha` remain separate
source/extraction obligations.
-/

section FiniteFamily

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

def rootTarget (p : K[X]) : Finset K := by
  classical
  exact p.roots.toFinset

theorem rootTarget_card_le (p : K[X]) :
    (rootTarget p).card ≤ p.natDegree := by
  classical
  exact (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

theorem evaluation_collision_mem_target (p : K[X]) (nonzero : p ≠ 0)
    (alpha : K) (collision : p.eval alpha = 0) : alpha ∈ rootTarget p := by
  classical
  change alpha ∈ p.roots.toFinset
  rw [Multiset.mem_toFinset]
  exact (Polynomial.mem_roots nonzero).mpr collision

def familyTarget (quarter claim : K) (sent : SameBodyRelation.Sent K) :
    List K[X] → Finset K
  | [] => ∅
  | honest :: rest =>
      rootTarget (actualCompactPolynomial quarter claim sent - honest) ∪
        familyTarget quarter claim sent rest

theorem family_target_card
    (quarter claim : K) (sent : SameBodyRelation.Sent K) :
    ∀ candidates : List K[X],
      (∀ p ∈ candidates, p.natDegree ≤ 6) →
      (familyTarget quarter claim sent candidates).card ≤ 6 * candidates.length := by
  classical
  intro candidates
  induction candidates with
  | nil => intro _; simp [familyTarget]
  | cons honest rest ih =>
    intro degree
    have headDegree := degree honest (by simp)
    have rootCap :
        (rootTarget (actualCompactPolynomial quarter claim sent - honest)).card ≤ 6 := by
      have deg := Polynomial.natDegree_sub_le (actualCompactPolynomial quarter claim sent) honest
      exact (rootTarget_card_le _).trans
        (deg.trans (max_le (actual_compact_degree quarter claim sent) headDegree))
    have tail := ih (by
      intro p member
      exact degree p (by simp [member]))
    have union := Finset.card_union_le
      (rootTarget (actualCompactPolynomial quarter claim sent - honest))
      (familyTarget quarter claim sent rest)
    rw [familyTarget]
    simp only [List.length_cons]
    omega

theorem collision_in_family_target
    (quarter claim alpha : K) (sent : SameBodyRelation.Sent K)
    (candidates : List K[X]) (honest : K[X]) (member : honest ∈ candidates)
    (different : actualCompactPolynomial quarter claim sent ≠ honest)
    (sourceCollision :
      (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic.evaluate7
        (SameBodyRelation.compact
          (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) alpha =
      honest.eval alpha) :
    alpha ∈ familyTarget quarter claim sent candidates := by
  classical
  have root : alpha ∈ rootTarget (actualCompactPolynomial quarter claim sent - honest) := by
    apply evaluation_collision_mem_target _ (sub_ne_zero.mpr different)
    rw [source_discrepancy_eval, sourceCollision, sub_self]
  induction candidates with
  | nil => simp at member
  | cons p ps ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact Finset.mem_union_left _ root
    · exact Finset.mem_union_right _ (ih tail)

/-- Equality of the actual compact polynomial and candidate is retained as a
separate non-probabilistic branch: `roots 0` cannot rule it out. -/
theorem classify_collision
    (quarter claim alpha : K) (sent : SameBodyRelation.Sent K)
    (candidates : List K[X]) (honest : K[X]) (member : honest ∈ candidates)
    (sourceCollision :
      (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic.evaluate7
        (SameBodyRelation.compact
          (SameBodyQueryClaimExact.ringArithmetic quarter).toArithmetic claim sent) alpha =
      honest.eval alpha) :
    actualCompactPolynomial quarter claim sent = honest ∨
      alpha ∈ familyTarget quarter claim sent candidates := by
  classical
  by_cases same : actualCompactPolynomial quarter claim sent = honest
  · exact Or.inl same
  · exact Or.inr (collision_in_family_target quarter claim alpha sent candidates honest
      member same sourceCollision)

end FiniteFamily

#print axioms actual_evaluate7_eq_ofFn_eval
#print axioms actual_compact_evaluation
#print axioms actual_compact_boundary
#print axioms source_discrepancy_eval
#print axioms family_target_card
#print axioms collision_in_family_target
#print axioms classify_collision

end
end AspisV8Completion.FSV8S4CompactEvaluationBridge

import SameBodyCompactTerminal
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
S5 FIRST ATTEMPT, UNCOMPILED. Replace an opaque Arithmetic.evaluate7 target
with the concrete degree-six source polynomial. Identical polynomials are
kept as a separate algebraic branch, NEVER called a rare challenge event.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
namespace AspisV8Completion.FSV8S5CompactPolynomialTarget
open Polynomial
open SameBodyQueryClaimExact SameBodyCompactTerminal
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
abbrev Coeff7 (K : Type*) := Fin 7 → K

def hstep (c : K) (p : Polynomial K) : Polynomial K := C c + X*p

def poly7 (c : Coeff7 K) : Polynomial K :=
  hstep (c 0) (hstep (c 1) (hstep (c 2) (hstep (c 3)
    (hstep (c 4) (hstep (c 5) (C (c 6)))))))

theorem hstep_natDegree_le (c : K) (p : Polynomial K) (n : Nat)
    (h : p.natDegree ≤ n) : (hstep c p).natDegree ≤ n+1 := by
  unfold hstep
  calc
    (C c + X*p).natDegree ≤ max (C c).natDegree (X*p).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ max 0 (1+n) := max_le (by simp) (by
      calc
        (X*p).natDegree ≤ X.natDegree+p.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1+n := by simpa only [Polynomial.natDegree_X] using Nat.add_le_add_left h 1)
    _ ≤ n+1 := by omega

theorem poly7_natDegree_le (c : Coeff7 K) : (poly7 c).natDegree ≤ 6 := by
  have h0 : (C (c 6) : Polynomial K).natDegree ≤ 0 := by simp
  have h1 := hstep_natDegree_le (c 5) _ 0 h0
  have h2 := hstep_natDegree_le (c 4) _ 1 h1
  have h3 := hstep_natDegree_le (c 3) _ 2 h2
  have h4 := hstep_natDegree_le (c 2) _ 3 h3
  have h5 := hstep_natDegree_le (c 1) _ 4 h4
  exact hstep_natDegree_le (c 0) _ 5 h5

theorem poly7_eval_is_source_fold (quarter : K) (c : Coeff7 K) (alpha : K) :
    (poly7 c).eval alpha = (ringArithmetic quarter).evaluate7 c alpha := by
  simp [poly7, hstep, ringArithmetic, List.ofFn_succ] <;> ring

/-- The actual compact decoder supplies c4 = claim*quarter-c0. -/
def compactPolynomial (quarter claim : K) (sent : SameBodyRelation.Sent K) : Polynomial K :=
  poly7 (SameBodyRelation.compact (ringArithmetic quarter).toArithmetic claim sent)

theorem compact_polynomial_eval (quarter claim alpha : K)
    (sent : SameBodyRelation.Sent K) :
    (compactPolynomial quarter claim sent).eval alpha =
      AspisV8.OptimizedRelationRefinement.sourceHorner quarter claim (parts sent) alpha := by
  unfold compactPolynomial
  rw [poly7_eval_is_source_fold quarter]
  exact compact_to_sourceHorner quarter claim alpha sent

theorem compact_polynomial_natDegree (quarter claim : K)
    (sent : SameBodyRelation.Sent K) :
    (compactPolynomial quarter claim sent).natDegree ≤ 6 := poly7_natDegree_le _

def difference (left right : Coeff7 K) : Coeff7 K := fun i => left i-right i

theorem poly7_difference (left right : Coeff7 K) :
    poly7 (difference left right) = poly7 left-poly7 right := by
  simp [poly7, hstep, difference, Polynomial.C_sub] <;> ring

def discrepancyRoots (left right : Coeff7 K) : Finset K :=
  (poly7 (difference left right)).roots.toFinset

/-- This is a cardinality statement about Polynomial.roots, which deliberately
returns no listed roots for the zero polynomial. Event equivalence below
therefore includes an explicit nonzero premise. -/
theorem discrepancy_roots_card_le (left right : Coeff7 K) :
    (discrepancyRoots left right).card ≤ 6 := by
  have subset : (discrepancyRoots left right).val ⊆
      (poly7 (difference left right)).roots := by
    intro a member
    simpa [discrepancyRoots] using member
  exact (Polynomial.card_le_degree_of_subset_roots subset).trans
    (poly7_natDegree_le _)

theorem nonzero_collision_mem_discrepancyRoots (left right : Coeff7 K) (alpha : K)
    (nonzero : poly7 (difference left right) ≠ 0)
    (collision : (poly7 left).eval alpha = (poly7 right).eval alpha) :
    alpha ∈ discrepancyRoots left right := by
  unfold discrepancyRoots
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots nonzero).mpr
  change (poly7 (difference left right)).eval alpha = 0
  rw [poly7_difference, Polynomial.eval_sub, collision]
  exact sub_self _

theorem collision_zero_or_listed (left right : Coeff7 K) (alpha : K)
    (collision : (poly7 left).eval alpha = (poly7 right).eval alpha) :
    poly7 (difference left right) = 0 ∨ alpha ∈ discrepancyRoots left right := by
  by_cases h : poly7 (difference left right) = 0
  · exact .inl h
  · exact .inr (nonzero_collision_mem_discrepancyRoots left right alpha h collision)

def familyRoots (claimed : Coeff7 K) : List (Coeff7 K) → Finset K
  | [] => ∅
  | reference :: rest => discrepancyRoots claimed reference ∪ familyRoots claimed rest

theorem family_roots_card_le (claimed : Coeff7 K) : ∀ references,
    (familyRoots claimed references).card ≤ 6*references.length := by
  intro references
  induction references with
  | nil => simp [familyRoots]
  | cons reference rest ih =>
      have h := Finset.card_union_le
        (discrepancyRoots claimed reference) (familyRoots claimed rest)
      have hroot := discrepancy_roots_card_le claimed reference
      simp only [familyRoots, List.length_cons]
      omega

theorem family_collision_zero_or_listed (claimed reference : Coeff7 K)
    (references : List (Coeff7 K)) (alpha : K)
    (member : reference ∈ references)
    (collision : (poly7 claimed).eval alpha = (poly7 reference).eval alpha) :
    poly7 (difference claimed reference) = 0 ∨ alpha ∈ familyRoots claimed references := by
  rcases collision_zero_or_listed claimed reference alpha collision with same | hit
  · exact .inl same
  · right
    revert member
    induction references with
    | nil => intro member; simp at member
    | cons head rest ih =>
        intro member
        rcases List.mem_cons.mp member with equal | later
        · subst reference
          exact Finset.mem_union.mpr (.inl hit)
        · exact Finset.mem_union.mpr (.inr (ih later))

/-- The provider must return actual coefficient vectors, not an arbitrary
scalar predicate or desired target cap. The reference-list SOURCE producer is
still required; this structure is NOT an extraction theorem. -/
structure CompactTargetData (count : Nat) (K : Type*) where
  quarter : K
  claim : K
  sent : SameBodyRelation.Sent K
  references : Fin count → Coeff7 K

def CompactTargetData.claimed {count : Nat} (data : CompactTargetData count K) : Coeff7 K :=
  SameBodyRelation.compact (ringArithmetic data.quarter).toArithmetic data.claim data.sent

def CompactTargetData.target {count : Nat} (data : CompactTargetData count K) : Finset K :=
  familyRoots data.claimed (List.ofFn data.references)

theorem CompactTargetData.target_card_le {count : Nat} (data : CompactTargetData count K) :
    data.target.card ≤ 6*count := by
  simpa [CompactTargetData.target] using family_roots_card_le data.claimed
    (List.ofFn data.references)

#print axioms compact_polynomial_eval
#print axioms compact_polynomial_natDegree
#print axioms discrepancy_roots_card_le
#print axioms collision_zero_or_listed
#print axioms CompactTargetData.target_card_le
end
end AspisV8Completion.FSV8S5CompactPolynomialTarget

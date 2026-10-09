import FSV8S5WordCovectorPolynomial

/-!
# S7 compact-word target inclusion

This leaf closes the algebraic seam between the concrete compact relation
polynomial and the concrete word/covector polynomial.  A false incoming claim
rules out the zero-discrepancy alternative, so an equality at `alpha` is a
member of the degree-six family target.

It does not construct the word/covector chunks, reference family, false-claim
fact, or source execution.  Those remain source producers of the eventual
ordinary-event theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

namespace AspisV8Completion.FSV8S7CompactWordTargetInclusion

open Polynomial
open FSV8S5CompactPolynomialTarget
open FSV8S5WordCovectorPolynomial
open SameBodyQueryClaimExact

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- The seven-coordinate Horner representation is injective.  This is the
small deterministic fact needed to turn a zero polynomial difference back
into equality of the actual compact coefficient vectors. -/
theorem poly7_injective : Function.Injective (poly7 : Coeff7 K → Polynomial K) := by
  intro left right equal
  funext i
  apply_fun (fun p : Polynomial K ↦ p.coeff i) at equal
  fin_cases i <;> simpa [poly7, hstep] using equal

theorem poly7_difference_ne_zero_of_ne (left right : Coeff7 K)
    (different : left ≠ right) :
    poly7 (difference left right) ≠ 0 := by
  intro zero
  apply different
  apply poly7_injective
  apply sub_eq_zero.mp
  rw [← poly7_difference]
  exact zero

/-- For the concrete word/covector reference, false claim binding eliminates
the identity branch of `family_collision_zero_or_listed`.  The only remaining
outcome is membership in the finite degree-six target.

The hypotheses are deliberately algebraic/source-facing inputs rather than a
caller-supplied target-inclusion premise. -/
theorem false_claim_collision_mem_familyRoots
    (quarter claim alpha : K) (fourQuarter : (4 : K) * quarter = 1)
    (sent : SameBodyRelation.Sent K)
    (chunks : List (Quad K × Quad K))
    (references : List (Coeff7 K))
    (referenceMember : wordCoefficients quarter chunks ∈ references)
    (falseClaim : claim ≠ wordDot chunks)
    (collision :
      (poly7 (SameBodyRelation.compact (ringArithmetic quarter).toArithmetic
          claim sent)).eval alpha =
        (poly7 (wordCoefficients quarter chunks)).eval alpha) :
    alpha ∈ familyRoots
      (SameBodyRelation.compact (ringArithmetic quarter).toArithmetic claim sent)
      references := by
  let claimed :=
    SameBodyRelation.compact (ringArithmetic quarter).toArithmetic claim sent
  let reference := wordCoefficients quarter chunks
  rcases family_collision_zero_or_listed claimed reference references alpha
      referenceMember collision with identity | listed
  · exfalso
    have coefficientDifferent : claimed ≠ reference := by
      exact different_claim_excludes_equal_coefficients quarter claim fourQuarter
        sent chunks falseClaim
    exact (poly7_difference_ne_zero_of_ne claimed reference coefficientDifferent)
      identity
  · exact listed

/-- The same result through the exact `CompactTargetData.target` interface
consumed by the routed ordinary probability theorem.  The selected reference
is exhibited from the finite source-produced family rather than supplied as
an already-proved target membership. -/
theorem false_claim_collision_mem_compactTarget
    {count : Nat} (data : CompactTargetData count K)
    (alpha : K) (fourQuarter : (4 : K) * data.quarter = 1)
    (chunks : List (Quad K × Quad K)) (index : Fin count)
    (referenceExact : data.references index =
      wordCoefficients data.quarter chunks)
    (falseClaim : data.claim ≠ wordDot chunks)
    (collision :
      (poly7 data.claimed).eval alpha =
        (poly7 (wordCoefficients data.quarter chunks)).eval alpha) :
    alpha ∈ data.target := by
  unfold CompactTargetData.target
  apply false_claim_collision_mem_familyRoots data.quarter data.claim alpha
    fourQuarter data.sent chunks (List.ofFn data.references)
  · exact List.mem_ofFn.mpr ⟨index, referenceExact⟩
  · exact falseClaim
  · simpa [CompactTargetData.claimed] using collision

#print axioms poly7_injective
#print axioms poly7_difference_ne_zero_of_ne
#print axioms false_claim_collision_mem_familyRoots
#print axioms false_claim_collision_mem_compactTarget

end
end AspisV8Completion.FSV8S7CompactWordTargetInclusion

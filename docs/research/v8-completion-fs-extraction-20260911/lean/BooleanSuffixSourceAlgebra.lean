import BooleanSuffixSourceConstructor

/-! Closure operations for local coordinate-slice source specifications.

These operations preserve the exact off-Boolean source value and its
one-coordinate polynomial restriction.  They do not infer an off-domain
identity from a Boolean table.  `mul` therefore requires the actual local
degree sum needed by the degree-27 selected grammar.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1000

namespace AspisV8Completion.BooleanSuffixSourceAlgebra
open scoped BigOperators
open Polynomial
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor

variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def zero : CoordinateSlices (K := K) where
  value := fun _ => 0
  slice := fun _ _ => 0
  degree := by intros; simp
  eval_at := by intros; simp

noncomputable def add (left right : CoordinateSlices (K := K)) :
    CoordinateSlices (K := K) where
  value := fun point => left.value point + right.value point
  slice := fun fixed round => left.slice fixed round + right.slice fixed round
  degree := by
    intro fixed round
    exact (natDegree_add_le _ _).trans (max_le (left.degree fixed round)
      (right.degree fixed round))
  eval_at := by
    intro fixed round x
    simp only [eval_add, left.eval_at, right.eval_at]

noncomputable def neg (spec : CoordinateSlices (K := K)) :
    CoordinateSlices (K := K) where
  value := fun point => -spec.value point
  slice := fun fixed round => -spec.slice fixed round
  degree := by
    intro fixed round
    simpa using spec.degree fixed round
  eval_at := by
    intro fixed round x
    simp only [eval_neg, spec.eval_at]

noncomputable def sub (left right : CoordinateSlices (K := K)) :
    CoordinateSlices (K := K) := add left (neg right)

noncomputable def scale (scalar : K) (spec : CoordinateSlices (K := K)) :
    CoordinateSlices (K := K) where
  value := fun point => scalar * spec.value point
  slice := fun fixed round => C scalar * spec.slice fixed round
  degree := by
    intro fixed round
    exact (natDegree_C_mul_le scalar _).trans (spec.degree fixed round)
  eval_at := by
    intro fixed round x
    simp only [eval_mul, eval_C, spec.eval_at]

/-- Product closure with its real local degree obligation.  Merely knowing
both factors have degree at most 27 would not justify their product. -/
noncomputable def mul (left right : CoordinateSlices (K := K))
    (degreeSum : ∀ fixed round,
      (left.slice fixed round).natDegree +
        (right.slice fixed round).natDegree ≤ 27) :
    CoordinateSlices (K := K) where
  value := fun point => left.value point * right.value point
  slice := fun fixed round => left.slice fixed round * right.slice fixed round
  degree := by
    intro fixed round
    exact natDegree_mul_le.trans (degreeSum fixed round)
  eval_at := by
    intro fixed round x
    simp only [eval_mul, left.eval_at, right.eval_at]

noncomputable def finsetSum {I : Type*} [Fintype I] [DecidableEq I]
    (spec : I → CoordinateSlices (K := K)) : CoordinateSlices (K := K) where
  value := fun point => ∑ index, (spec index).value point
  slice := fun fixed round => ∑ index, (spec index).slice fixed round
  degree := by
    intro fixed round
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro index _
    exact (spec index).degree fixed round
  eval_at := by
    intro fixed round x
    simp only [Polynomial.eval_finsetSum, (spec _).eval_at]

theorem add_value (left right : CoordinateSlices (K := K)) (point : Fin 10 → K) :
    (add left right).value point = left.value point + right.value point := rfl

theorem mul_value (left right : CoordinateSlices (K := K))
    (degreeSum : ∀ fixed round,
      (left.slice fixed round).natDegree +
        (right.slice fixed round).natDegree ≤ 27)
    (point : Fin 10 → K) :
    (mul left right degreeSum).value point =
      left.value point * right.value point := rfl

theorem finsetSum_value {I : Type*} [Fintype I] [DecidableEq I]
    (spec : I → CoordinateSlices (K := K)) (point : Fin 10 → K) :
    (finsetSum spec).value point = ∑ index, (spec index).value point := rfl

#print axioms zero
#print axioms add
#print axioms neg
#print axioms scale
#print axioms mul
#print axioms finsetSum
end AspisV8Completion.BooleanSuffixSourceAlgebra

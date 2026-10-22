import MultiproofConeCountLevels

set_option autoImplicit false
namespace AspisR1.MultiproofConeCountBounds
open OraclePortFrozenOrder MultiproofConeCountLevels
attribute [local instance] Classical.propDecidable

theorem level_bounds (fuel : Nat) (is : List Nat) :
    (countLevel fuel is).1.length≤fuel ∧ (countLevel fuel is).2≤fuel := by
  induction fuel generalizing is with
  | zero => simp [countLevel]
  | succ fuel ih =>
    cases is with
    | nil => simp [countLevel]
    | cons i rest =>
      let both : Bool := match rest with | j::_ => decide (paired i j) | [] => false
      let tail := if both then rest.drop 1 else rest
      have bound := ih tail
      change (countLevel fuel tail).1.length+1≤fuel+1 ∧
        (countLevel fuel tail).2+(if both then 0 else 1)≤fuel+1
      have small : (if both then 0 else 1 : Nat)≤1 := by split <;> omega
      exact ⟨by omega,by omega⟩

/-- The entire source count accumulation fits usize with large margin; each
level has at most sixteen groups, each contributing at most one sibling. -/
theorem count_bound (height : Nat) (is : List Nat) (size : is.length≤16)
    (order : is.Pairwise (·<·)) : sourceCount height is≤16*height := by
  rw [count_eq height is order]
  induction height generalizing is with
  | zero => exact Nat.le_refl _
  | succ height ih =>
    rw [nodeCount]
    have level := level_bounds is.length is
    have future := ih (countLevel is.length is).1 (by omega) (sorted _ _ order)
    omega

theorem eighteen_bound (is : List Nat) (size : is.length≤16) (order : is.Pairwise (·<·)) :
    sourceCount 18 is≤288 := count_bound 18 is size order

#print axioms level_bounds
#print axioms count_bound
#print axioms eighteen_bound
end AspisR1.MultiproofConeCountBounds

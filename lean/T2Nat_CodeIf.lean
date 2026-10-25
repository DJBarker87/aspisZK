import T2Nat_CodeEq
set_option autoImplicit false
namespace AspisR1.T2Nat_CodeIf
open CheckpointBytes5Effect T2Nat_CodeEq

theorem branches {A : Type} (p : Prop) [Decidable p]
    (leftYes leftNo rightYes rightNo : Code A)
    (yes : EqRun leftYes rightYes) (no : EqRun leftNo rightNo) :
    EqRun (if p then leftYes else leftNo) (if p then rightYes else rightNo) := by
  by_cases h : p
  · simpa only [if_pos h] using yes
  · simpa only [if_neg h] using no

#print axioms branches
end AspisR1.T2Nat_CodeIf

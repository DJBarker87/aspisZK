import R1Z.BuilderTreeStepExtracted
import R1Z.BuilderTreeCarry

set_option autoImplicit false
namespace R1Z.BuilderTreeStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderTreeReference.pool_v1.incremental_merkle.tree_reference
open BuilderTreeCarry

theorem callback_step {H : Type} (parent : Parent H) (frontier empty carry : Digest)
    (level : Usize) (state : H) :
    carry_step_owned parent frontier empty carry level state = (do
      let (next,_) ← parent.call_mut state (frontier,carry)
      ok (next,empty,Usize.wrapping_add level 1#usize)) := by
  rw [carry_step_owned]
  rfl

theorem callback_success {H : Type} (parent : Parent H) (frontier empty carry next : Digest)
    (level : Usize) (state after : H)
    (h : parent.call_mut state (frontier,carry) = ok (next,after)) :
    carry_step_owned parent frontier empty carry level state =
      ok (next,empty,Usize.wrapping_add level 1#usize) := by
  rw [callback_step,h]
  rfl

/-- Complete array frame law supplying the array part of the projected P6 step. -/
theorem clear_step (frontier : Frontier) (empty : Roots) (level : Usize)
    (hl : level.val < 20) (j : Nat) :
    (frontier.set level empty.val[level.val]!).val[j]! =
      if j = level.val then empty.val[j]! else frontier.val[j]! := by
  rw [BuilderRecordsArray.set_get _ _ _ _ (by simpa using hl)]
  by_cases h : j = level.val
  · subst j; rfl
  · rw [if_neg h,if_neg h]

#print axioms callback_step
#print axioms callback_success
#print axioms clear_step
end R1Z.BuilderTreeStep

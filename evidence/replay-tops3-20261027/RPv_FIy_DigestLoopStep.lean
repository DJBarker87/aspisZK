import RPv_FIy_DigestLane
set_option autoImplicit false
namespace AspisR1.FIy_DigestLoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev loop := pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop

theorem value (r : core.ops.range.Range Usize) (output : Array NQ 8#usize)
    (selector : NQ) (opened : Array NQ 16#usize) (start : Usize)
    (expected : Array U32 8#usize) (right : Bool) :
    loop r output selector opened start expected right=(do
      let (o,r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      match o with
      | none=>ok output
      | some lane=>do
        let next ← FIy_DigestLane.run lane output selector opened start expected right
        loop r' next selector opened start expected right) := by
  rw [loop,pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop]
  cases right <;>
    simp only [FIy_DigestLane.run,FIy_DigestTarget.run,FIy_DigestArithmetic.run,bind_assoc_eq]
  all_goals
    congr 1 <;> (
    funext p
    rcases p with ⟨opt,r'⟩
    cases opt with
    | none=>rfl
    | some lane=>
      congr 1
      funext target
      simp only [Bool.false_eq_true,↓reduceIte,bind_tc_ok,bind_assoc_eq]
      rfl)
#print axioms value
end AspisR1.FIy_DigestLoopStep

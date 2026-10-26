import FIy_FrontierStep
set_option autoImplicit false
namespace AspisR1.FIy_FrontierLoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIy_FrontierStep (Snapshot Selectors)
abbrev loop := pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop

theorem value (r : core.ops.range.Range Usize) (a : Array NQ 16#usize) (s : Selectors)
    (d : Array NQ 8#usize) (src : Snapshot) :
    loop r a s d src=(do
      let (o,r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      match o with
      | none=>ok (d,src)
      | some level=>do
        let next ← FIy_FrontierStep.run level a s d src
        loop r' a s next src) := by
  rw [loop,pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop]
  simp only [FIy_FrontierStep.run,bind_assoc_eq]
  congr 1
  funext p
  rcases p with ⟨opt,r'⟩
  cases opt with
  | none=>rfl
  | some level=>
    congr 1
    funext block
    congr 1
    funext i
    simp only [lift,bind_tc_ok]
    split <;> simp only [bind_assoc_eq,bind_tc_ok]
    all_goals rfl
#print axioms value
end AspisR1.FIy_FrontierLoopStep

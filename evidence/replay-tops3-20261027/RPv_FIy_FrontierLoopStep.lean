import RPv_FIy_FrontierStep
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
  apply congrArg (fun k => core.iter.range.IteratorRange.next core.iter.range.StepUsize r >>= k)
  funext p
  rcases p with ⟨opt,r'⟩
  cases opt with
  | none=>rfl
  | some level=>
    apply congrArg (fun k => (34#usize+level) >>= k)
    funext block
    apply congrArg (fun k => (src.next_pair_index >>> level) >>= k)
    funext i
    simp only [lift,bind_tc_ok]
    split <;> simp only [bind_assoc_eq,bind_tc_ok]
    all_goals rfl
#print axioms value
end AspisR1.FIy_FrontierLoopStep

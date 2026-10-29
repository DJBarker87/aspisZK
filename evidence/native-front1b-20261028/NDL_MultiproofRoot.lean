import NDL_MultiproofAccess
set_option autoImplicit false
noncomputable section
namespace NDL_MultiproofRoot
open Aeneas Aeneas.Std Result MultiproofConeRef
attribute [local instance] Classical.propDecidable

/-- The existing terminal root predicate consumes the SAME physical out.val[0].
All n/index/cursor checks remain present, rather than promoting root equality
alone to verification success. -/
theorem source_guard (root : Array U8 32#usize) (physical : Slice U8) (s : reference.Scratch) :
    (do
      let rootSame ← NDD_Reference.root_ref s.val root
      ok (decide (s.n.val=1 ∧ s.idx.val[0]!.val=0 ∧ rootSame=true ∧
        s.«at».val=physical.val.length))) =
      ok (AspisR1.MultiproofConeRootGuard.sourceRoot root physical s) := by
  rw [NDL_MultiproofAccess.root_matches]
  simp only [bind_tc_ok,AspisR1.MultiproofConeRootGuard.sourceRoot,
    decide_eq_true_eq,NCJ_GuardExact.pick]
  have len : 0<s.val.val.length := by rw [s.val.property];decide
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some]

#print axioms source_guard
end NDL_MultiproofRoot
end

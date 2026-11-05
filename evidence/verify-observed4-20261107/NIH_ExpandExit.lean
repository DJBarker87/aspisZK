import NIH_ExpandOuter
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_ExpandExit
open FIq_Native
/-- The terminal iterator stage needs no len<=N/2 premise. In particular len=N
at both actual expansion exits is included. -/
theorem result {N : Usize} (iter : core.slice.iter.Iter field.QM31)
 (weights : Array field.QM31 N) (len : Usize) (done : iter.slice.val.length ≤ iter.i) :
 pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter weights len=ok weights := by
 rw [NIH_ExpandOuter.stage]
 have stopped : ¬ (iter.i < iter.slice.val.length) := by omega
 simp only [core.slice.iter.IteratorSliceIter.next,Slice.len_val,stopped,↓reduceDIte,bind_tc_ok]
 rfl
#print axioms result
end AspisR1.NIH_ExpandExit
end

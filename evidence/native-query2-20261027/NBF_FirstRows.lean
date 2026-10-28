import NBF_RowsTotal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_FirstRows
open AspisR1 AspisR1Stage2
/-- The SAME successful emitted pending constructor supplies initial row
progress. This merely imports the checked constructor/initialization bridge. -/
theorem constructor_progress (reserved : Bool) (old : Slice NBF_RowInstall.Q)
 (b : verifier.BatchedWeights) (size : old.val.length=64)
 (run : Port3_NativePendingInstall.source reserved old=ok (.Ok b)) :
 b.terms=0#usize ∧ S7JoinRowsTrace.Progress 0 0 (Port3_RowsInstall.toBW b) := by
 have reference := Port3_NativePendingInstall.reference_eq reserved old size
 have accepted : Port3_PendingInstall.pending reserved old=ok (.Ok b) := reference.symm.trans run
 exact ⟨(Port3_PendingInstall.accepted_fields reserved old b accepted).2.2.1,
   Port3_PendingInstall.accepted_progress reserved old b size accepted⟩

/-- First complete emitted row traversal: no input row-phase witness is
assumed. It comes from the actual successful constructor on THAT old vector. -/
theorem first (ops : Port3_NativeQueryBody.Ops) (reserved : Bool)
 (old : Slice NBF_RowInstall.Q) (v : alloc.vec.Vec NBF_RowInstall.Q)
 (q : NBF_RowInstall.Q) (next : Usize) (basis : Array U32 256#usize)
 (b : verifier.BatchedWeights) (size : old.val.length=64) (v64 : v.val.length=64)
 (constructor : Port3_NativePendingInstall.source reserved old=ok (.Ok b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1)
 (hb : ∀ j : Usize, j.val<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1) :
 ∃ out, Port3_NativeQueryBody.verifier.accumulate_batched_with_node_loop1 (NBF_RowInstall.install ops)
   {start:=0#usize,«end»:=64#usize} v q next b 64#usize basis=ok out ∧
 out.terms=0#usize ∧ out.raw.val.length=64 ∧
 ∀ (j : Nat) (row : NBF_Frame.Row), out.raw.val[j]?=some row → NBB_Sweep.Bound 1 row := by
 obtain ⟨terms,progress⟩ := constructor_progress reserved old b size constructor
 have progress1 : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b) := by
   simpa only [terms,show (0#usize).val=0 from rfl] using progress
 obtain ⟨out,run,same,len,phase⟩ := NBF_RowsTotal.full ops v q next basis b v64 progress1 hq hb
 exact ⟨out,run,same.trans terms,len,by simpa only [terms,show (0#usize).val=0 from rfl] using phase⟩
#print axioms constructor_progress
#print axioms first
end NBF_FirstRows

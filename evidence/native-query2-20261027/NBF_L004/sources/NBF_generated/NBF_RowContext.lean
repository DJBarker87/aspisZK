import NBF_Read
import Port3_NativeRowLoop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NBF_RowContext
open AspisR1Stage2
open AspisR1.Port3_NativeQueryBody
open AspisR1 (Port3_NativeRowFrame)
/-- Successful actual owned push is exactly one setter at the reached index.
The setter is derived by inverting its concrete continuation. -/
theorem push_write (b out : verifier.BatchedWeights) (j : Usize)
 (q : aspis_core.field.QM31) (m : U32) (inRange : j.val<b.raw.val.length)
 (run : Port3_NativeRowFrame.push b j q m=ok out) :
 ∃ row : NBF_Frame.Row, out={b with raw:=b.raw.set j row} := by
 unfold Port3_NativeRowFrame.push at run
 obtain ⟨mid,hpush,finish⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
 unfold S7Kani2OwnedPush.push_owned at hpush
 obtain ⟨old,hread,hpush⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ hpush
 obtain ⟨flag,hflag,hpush⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ hpush
 obtain ⟨row,hrow,hpush⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ hpush
 obtain ⟨⟨borrowed,back⟩,hborrow,hpush⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ hpush
 obtain ⟨⟨borrowed1,back1⟩,hmut,_,hback⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.index_mut_usize_spec b.raw j inRange)
 have eq : (borrowed,back)=(borrowed1,back1) := by
   have same : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice NBF_Frame.Row)
     b.raw j=ok (borrowed1,back1) := by
       rw [alloc.vec.Vec.index_mut_slice_index];exact hmut
   exact Result.ok.inj (hborrow.symm.trans same)
 cases eq
 cases Result.ok.inj hpush
 cases Result.ok.inj finish
 exact ⟨row,by simp only [AspisR1.Port3_RowsInstall.toBW,
   AspisR1.Port3_RowsInstall.fromBW,hback]⟩

/-- One actual emitted row-loop body reaches one owned setter; all earlier
and later trace operations are retained in the observed successful body. -/
theorem body_write (ops : Ops) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (next width : Usize)
 (basis : Array U32 256#usize) (iter : core.ops.range.Range Usize)
 (b : verifier.BatchedWeights)
 (active : iter.start.val<iter.end.val) (bound : iter.end.val≤b.raw.val.length)
 (out : ControlFlow (core.ops.range.Range Usize × verifier.BatchedWeights) verifier.BatchedWeights)
 (run : verifier.accumulate_batched_with_node_loop1.body
   (Port3_NativeRowFrame.install ops) v q next width basis iter b=ok out) :
 ∃ iter1 row, out=cont (iter1,{b with raw:=b.raw.set iter.start row}) ∧
   iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end := by
 obtain ⟨⟨o,iter1⟩,hr,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl) iter active)
 subst o
 unfold verifier.accumulate_batched_with_node_loop1.body at run
 rw [hr] at run
 simp only [bind_tc_ok] at run
 obtain ⟨m,hm,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨b1,hpush,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨row,same⟩ := push_write b b1 iter.start q m (by omega) hpush
 subst b1
 iterate 9 obtain ⟨x,hx,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
 exact ⟨iter1,row,(Result.ok.inj run).symm,hs,he⟩
#print axioms push_write
#print axioms body_write
end NBF_RowContext

import NBF_Progress
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NBF_RowsTotal
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Finite induction over the actual emitted row loop, using the inherited
phase progress witness at every reached pre-state. No accepted output premise. -/
theorem total (ops : Ops) (v : alloc.vec.Vec NBF_RowInstall.Q)
 (q : NBF_RowInstall.Q) (next : Usize) (basis : Array U32 256#usize)
 (fuel : Nat) (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights)
 (t : Nat) (width : iter.end.val=64) (span : iter.start.val+fuel=64)
 (v64 : v.val.length=64)
 (progress : S7JoinRowsTrace.Progress t iter.start.val (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1)
 (hb : ∀ j : Usize, j.val<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1) :
 ∃ out, verifier.accumulate_batched_with_node_loop1 (NBF_RowInstall.install ops)
   iter v q next b 64#usize basis=ok out ∧
 S7JoinRowsTrace.Progress t 64 (Port3_RowsInstall.toBW out) := by
 induction fuel generalizing iter b with
 | zero =>
   have done : iter.end.val≤iter.start.val := by omega
   have stop := Port3_NativeRowLoop.stopped (NBF_RowInstall.install ops)
     v q next 64#usize basis iter b done
   refine ⟨b,?_,by simpa only [show iter.start.val=64 by omega] using progress⟩
   unfold verifier.accumulate_batched_with_node_loop1
   rw [Aeneas.Std.loop.eq_def]
   simp only [Aeneas.Std.uncurry,stop,bind_tc_ok]
 | succ n ih =>
   obtain ⟨iter1,b1,step,start,finish,progress1⟩ := NBF_Progress.body ops v q next basis
     iter b t width (by omega) v64 progress hq hb
   obtain ⟨out,tail,progressOut⟩ := ih iter1 b1 (by rw [finish];exact width)
     (by omega) progress1
   refine ⟨out,?_,progressOut⟩
   unfold verifier.accumulate_batched_with_node_loop1
   rw [Aeneas.Std.loop.eq_def]
   simp only [Aeneas.Std.uncurry,step,bind_tc_ok]
   exact tail

/-- Every64-row traversal from cursor0 is total and establishes the next
phase for every row on the SAME actual output carrier. -/
theorem full (ops : Ops) (v : alloc.vec.Vec NBF_RowInstall.Q)
 (q : NBF_RowInstall.Q) (next : Usize) (basis : Array U32 256#usize)
 (b : verifier.BatchedWeights) (v64 : v.val.length=64)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1)
 (hb : ∀ j : Usize, j.val<64 → ∀ m, Array.index_usize basis j=ok m → m.val<2^31-1) :
 ∃ out, verifier.accumulate_batched_with_node_loop1 (NBF_RowInstall.install ops)
   {start:=0#usize,«end»:=64#usize} v q next b 64#usize basis=ok out ∧
 out.terms=b.terms ∧ out.raw.val.length=64 ∧
 ∀ j row, out.raw.val[j]?=some row → NBB_Sweep.Bound (b.terms.val+1) row := by
 obtain ⟨out,run,hp⟩ := total ops v q next basis 64
   {start:=0#usize,«end»:=64#usize} b b.terms.val (by rfl) (by rfl) v64 progress hq hb
 have sweep := NBF_Progress.sweep b.terms.val 64 out hp
 refine ⟨out,run,?_,hp.2.1,?_⟩
 · apply UScalar.eq_of_val_eq;exact hp.1
 · intro j row read
   have hi : j<64 := by have len : out.raw.val.length=64:=hp.2.1
                       have := (List.getElem?_eq_some_iff.mp read).1;omega
   simpa only [if_pos hi] using sweep j row read
#print axioms total
#print axioms full
end NBF_RowsTotal

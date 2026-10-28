import NBF_RowsTotal
import S7Kani2BasisLoop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NBF_Basis
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- One emitted basis body is the inherited S7 block step. The only field
operation is the SAME explicit op7; bounded checked/wrapping offsets agree. -/
theorem step (ops : Ops) (node : U32) (n : Usize)
 (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
 (hn : n.val≤128) (finish : iter.end=n) (active : iter.start.val < n.val) :
 ∃ iter1, iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 verifier.accumulate_batched_with_node_loop0_loop0.body ops node n iter basis=
   (do let out ← S7Kani2BasisLoop.step ops.op7 node n iter.start basis
       ok (cont (iter1,out))) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
     iter (by rw [finish];exact active))
 subst o
 have add := Port3_Wrapping.checked_add n iter.start (by omega)
 refine ⟨iter1,hs,he,?_⟩
 simp [verifier.accumulate_batched_with_node_loop0_loop0.body,run,
   S7Kani2BasisLoop.step,add,lift]

theorem stop (ops : Ops) (node : U32) (n : Usize)
 (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
 (done : iter.end.val ≤ iter.start.val) :
 verifier.accumulate_batched_with_node_loop0_loop0.body ops node n iter basis=ok (.done basis) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_none_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter done)
 subst o
 simp [verifier.accumulate_batched_with_node_loop0_loop0.body,run]

/-- Result-valued association, preserving first failure/divergence, for the
actual native inner loop and inherited bounded S7 composition. -/
theorem iterate (ops : Ops) (node : U32) (n : Usize)
 (fuel : Nat) (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
 (hn : n.val≤128) (finish : iter.end=n) (span : iter.start.val+fuel=n.val) :
 verifier.accumulate_batched_with_node_loop0_loop0 ops iter node basis n=
 S7Kani2BasisLoop.iterate (S7Kani2BasisLoop.step ops.op7 node n) fuel iter.start basis := by
 induction fuel generalizing iter basis with
 | zero =>
   unfold verifier.accumulate_batched_with_node_loop0_loop0
   rw [Aeneas.Std.loop.eq_def]
   have halt := stop ops node n iter basis (by rw [finish];omega)
   simp only [halt,S7Kani2BasisLoop.iterate,bind_tc_ok]
 | succ k ih =>
   obtain ⟨iter1,hs,he,body⟩ := step ops node n iter basis hn finish (by omega)
   have inc := Port3_Wrapping.checked_add iter.start 1#usize (by change iter.start.val+1≤4096;omega)
   have idx : Usize.wrapping_add iter.start 1#usize=iter1.start := by
     apply UScalar.eq_of_val_eq
     rw [Port3_Wrapping.increment iter.start (by omega),hs]
   unfold verifier.accumulate_batched_with_node_loop0_loop0
   rw [Aeneas.Std.loop.eq_def]
   simp only [body,S7Kani2BasisLoop.iterate,bind_assoc_eq,inc,idx,bind_tc_ok]
   cases run : S7Kani2BasisLoop.step ops.op7 node n iter.start basis with
   | fail e => simp only [bind_tc_fail]
   | div => simp only [bind_tc_div]
   | ok out =>
     simp only [bind_tc_ok]
     exact ih iter1 out (he.trans finish) (by omega)
#print axioms step
#print axioms stop
#print axioms iterate
end NBF_Basis

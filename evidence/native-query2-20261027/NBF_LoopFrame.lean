import NBF_RowContext
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace NBF_LoopFrame
open AspisR1 AspisR1Stage2
open Port3_NativeQueryBody
theorem append {start count n : Nat} {before mid after : NBF_Frame.Raw}
 (prior : NBF_Frame.Writes start count before mid)
 (following : NBF_Frame.Writes (start+count) n mid after) :
 NBF_Frame.Writes start (count+n) before after := by
 induction following with
 | nil => simpa only [Nat.add_zero] using prior
 | @step c first last p index row cursor inside ih =>
   have cursor1 : index.val=start+(count+c) := by omega
   simpa only [Nat.add_assoc] using
     NBF_Frame.Writes.step (ih prior) index row cursor1 inside

/-- Actual emitted row traversal constructs the linked setter trace. No
complete vector frame or preselected output is a hypothesis. -/
theorem writes (ops : Ops) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (next width : Usize) (basis : Array U32 256#usize)
 (fuel : Nat) (iter : core.ops.range.Range Usize) (b out : verifier.BatchedWeights)
 (span : iter.start.val+fuel=iter.end.val) (bound : iter.end.val≤b.raw.val.length)
 (accepted : verifier.accumulate_batched_with_node_loop1 (Port3_NativeRowFrame.install ops)
   iter v q next b width basis=ok out) :
 NBF_Frame.Writes iter.start.val fuel b.raw out.raw ∧ out.terms=b.terms := by
 induction fuel generalizing iter b with
 | zero =>
   unfold verifier.accumulate_batched_with_node_loop1 at accepted
   rw [Aeneas.Std.loop.eq_def] at accepted
   simp only [Aeneas.Std.uncurry] at accepted
   have halt := Port3_NativeRowLoop.stopped (Port3_NativeRowFrame.install ops)
     v q next width basis iter b (by omega)
   simp only [halt,bind_tc_ok] at accepted
   cases Result.ok.inj accepted
   exact ⟨.nil _ _,rfl⟩
 | succ n ih =>
   unfold verifier.accumulate_batched_with_node_loop1 at accepted
   rw [Aeneas.Std.loop.eq_def] at accepted
   simp only [Aeneas.Std.uncurry] at accepted
   generalize step : verifier.accumulate_batched_with_node_loop1.body
     (Port3_NativeRowFrame.install ops) v q next width basis iter b = r at accepted
   cases r with
   | fail e => cases accepted
   | div => cases accepted
   | ok cf =>
     obtain ⟨iter1,row,same,hs,he⟩ := NBF_RowContext.body_write
       ops v q next width basis iter b (by omega) bound cf step
     subst cf
     change verifier.accumulate_batched_with_node_loop1 (Port3_NativeRowFrame.install ops)
       iter1 v q next {b with raw:=b.raw.set iter.start row} width basis=ok out at accepted
     have bound1 : iter1.end.val≤(b.raw.set iter.start row).val.length := by
       change iter1.end.val ≤ (b.raw.val.set iter.start.val row).length
       rw [List.length_set,he];exact bound
     obtain ⟨tail,terms⟩ := ih iter1 {b with raw:=b.raw.set iter.start row}
       (by rw [he];omega) bound1 accepted
     refine ⟨?_,terms⟩
     -- Prepend the first setter to the recursively constructed suffix.
     have first : NBF_Frame.Writes iter.start.val 1 b.raw
       (b.raw.set iter.start row) :=
       .step (.nil _ _) iter.start row (by omega) (by omega)
     have tail1 : NBF_Frame.Writes (iter.start.val+1) n
       (b.raw.set iter.start row) out.raw := by simpa only [hs] using tail
     simpa only [Nat.add_comm 1 n] using append first tail1

/-- All rows outside the actual emitted traversal window retain their original
contents, including arbitrary suffixes. Length and terms are also unchanged. -/
theorem frame (ops : Ops) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (next width : Usize) (basis : Array U32 256#usize)
 (fuel : Nat) (iter : core.ops.range.Range Usize) (b out : verifier.BatchedWeights)
 (span : iter.start.val+fuel=iter.end.val) (bound : iter.end.val≤b.raw.val.length)
 (accepted : verifier.accumulate_batched_with_node_loop1 (Port3_NativeRowFrame.install ops)
   iter v q next b width basis=ok out) :
 out.raw.val.length=b.raw.val.length ∧ out.terms=b.terms ∧
 ∀ j, j < iter.start.val ∨ iter.end.val≤j → out.raw.val[j]?=b.raw.val[j]? := by
 obtain ⟨trace,terms⟩ := writes ops v q next width basis fuel iter b out span bound accepted
 exact ⟨NBF_Frame.length trace,terms,fun j outside =>
   NBF_Frame.outside trace j (by omega)⟩
#print axioms append
#print axioms writes
#print axioms frame
end NBF_LoopFrame

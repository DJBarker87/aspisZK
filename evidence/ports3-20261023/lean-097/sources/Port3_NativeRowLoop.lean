import Port3_NativeRowFrame

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeRowLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeQueryBody

theorem stopped (ops : Ops) (v : alloc.vec.Vec aspis_core.field.QM31)
    (q : aspis_core.field.QM31) (next width : Usize) (basis : Array U32 256#usize)
    (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights)
    (done : iter.end.val ≤ iter.start.val) :
    verifier.accumulate_batched_with_node_loop1.body ops v q next width basis iter b=ok (.done b) := by
  obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b; rfl) iter done)
  subst o
  unfold verifier.accumulate_batched_with_node_loop1.body
  rw [run]
  rfl

/-- Symbolic finite induction over the emitted row traversal. A successful
push is inspected at its actual reached index, never evaluated concretely64 times. -/
theorem fields (ops : Ops) (v : alloc.vec.Vec aspis_core.field.QM31)
    (q : aspis_core.field.QM31) (next width : Usize) (basis : Array U32 256#usize)
    (fuel : Nat) (iter : core.ops.range.Range Usize) (b out : verifier.BatchedWeights)
    (span : iter.start.val+fuel=iter.end.val) (bound : iter.end.val≤b.raw.val.length)
    (accepted : verifier.accumulate_batched_with_node_loop1 (Port3_NativeRowFrame.install ops)
      iter v q next b width basis=ok out) :
    out.raw.val.length=b.raw.val.length ∧ out.terms=b.terms := by
  induction fuel generalizing iter b with
  | zero =>
    unfold verifier.accumulate_batched_with_node_loop1 at accepted
    rw [Aeneas.Std.loop.eq_def] at accepted
    simp only [Aeneas.Std.uncurry] at accepted
    have halt := stopped (Port3_NativeRowFrame.install ops) v q next width basis iter b (by omega)
    simp only [halt,bind_tc_ok] at accepted
    cases Result.ok.inj accepted
    exact ⟨rfl,rfl⟩
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
      obtain ⟨iter1,b1,same,hs,he,hlen,hterms⟩ :=
        Port3_NativeRowFrame.body_fields ops v q next width basis iter b (by omega) bound cf step
      subst cf
      change verifier.accumulate_batched_with_node_loop1 (Port3_NativeRowFrame.install ops)
        iter1 v q next b1 width basis=ok out at accepted
      have final := ih iter1 b1 (by rw [he]; omega) (by rw [he,hlen]; exact bound) accepted
      exact ⟨final.1.trans hlen,final.2.trans hterms⟩

#print axioms stopped
#print axioms fields
end AspisR1.Port3_NativeRowLoop
end

import NEV_AccumulateRaw.Funs
import NEI_FieldScalar
import NBF_BasisInstall
set_option autoImplicit false
noncomputable section
namespace NEV_BasisRaw
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- New actual-body association only. Arithmetic is the imported closed field
bridge, and the recurrence/induction below is the retained NBF/S7 recurrence. -/
theorem inner_step (ops : Ops) (node : U32) (n : Usize)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (small : n.val≤128) (finish : iter.end=n) (active : iter.start.val<n.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body node n iter basis =
      verifier.accumulate_batched_with_node_loop0_loop0.body
        (NBF_BasisInstall.install ops) node n iter basis := by
  obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter (by rw [finish];exact active))
  subst o
  have add := Port3_Wrapping.checked_add n iter.start (by omega)
  simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body,
    verifier.accumulate_batched_with_node_loop0_loop0.body,run,bind_tc_ok,
    NEV_AccumulateRaw.aspis_core.field.M31.mul,NEI_FieldScalar.m_mul,
    AspisR1CurrentWide.Proof.m31_mul_same,NBF_BasisInstall.install,add,lift]
  dsimp only
  simp only [add,bind_tc_ok]

theorem inner_stop (ops : Ops) (node : U32) (n : Usize)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (done : iter.end.val≤ iter.start.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body node n iter basis =
      verifier.accumulate_batched_with_node_loop0_loop0.body
        (NBF_BasisInstall.install ops) node n iter basis := by
  obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter done)
  subst o
  simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0.body,
    verifier.accumulate_batched_with_node_loop0_loop0.body,run,bind_tc_ok]
  rfl

/-- The only new induction transports the newly imported checked Rust loop to
its already-proved NBF emitted loop. No basis arithmetic is reproved. -/
theorem inner_loop (ops : Ops) (node : U32) (n : Usize) (fuel : Nat)
    (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize)
    (small : n.val≤128) (finish : iter.end=n) (span : iter.start.val+fuel=n.val) :
    NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0 iter node basis n =
      verifier.accumulate_batched_with_node_loop0_loop0 (NBF_BasisInstall.install ops)
        iter node basis n := by
  induction fuel generalizing iter basis with
  | zero =>
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0
      verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    have done : iter.end.val≤ iter.start.val := by rw [finish];omega
    rw [inner_stop ops node n iter basis done]
    rw [NBF_Basis.stop (NBF_BasisInstall.install ops) node n iter basis done]
    rfl
  | succ k ih =>
    have active : iter.start.val<n.val := by omega
    obtain ⟨iter1,hs,he,body⟩ := NBF_Basis.step (NBF_BasisInstall.install ops)
      node n iter basis small finish active
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop0_loop0
      verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    rw [inner_step ops node n iter basis small finish active,body]
    simp only [bind_assoc_eq,bind_tc_ok]
    cases step : S7Kani2BasisLoop.step (NBF_BasisInstall.install ops).op7 node n iter.start basis with
    | fail e => simp only [step,bind_tc_fail]
    | div => simp only [step,bind_tc_div]
    | ok out =>
      simp only [step,bind_tc_ok]
      exact ih iter1 out (he.trans finish) (by omega)

#print axioms inner_step
#print axioms inner_stop
#print axioms inner_loop
end NEV_BasisRaw
end

import Port4C_RowMeaning

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_BasisInner
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
abbrev Basis := Array U32 256#usize

theorem body (ops : Ops) (node : U32) (n : Usize) (basis : Basis)
    (iter iter1 : core.ops.range.Range Usize) (j : Usize)
    (small : n.val+j.val≤4096)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some j,iter1)) :
    verifier.accumulate_batched_with_node_loop0_loop0.body ops node n iter basis =
      (do let basis1 ← S7Kani2BasisLoop.step ops.op7 node n j basis
          ok (cont (iter1,basis1))) := by
  unfold verifier.accumulate_batched_with_node_loop0_loop0.body S7Kani2BasisLoop.step
  rw [next,bind_tc_ok,Port3_Wrapping.checked_add n j small]
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

/-- Full CURRENT native block transport, with arbitrary primitive multiply.
Wrapping index and iterator progress are bounded independently of field laws. -/
theorem from_iterate (ops : Ops) (node : U32) (n : Usize)
    (iter : core.ops.range.Range Usize) (basis out : Basis) (fuel : Nat)
    (bound : n.val≤128) (ending : iter.end=n)
    (span : iter.start.val+fuel=n.val)
    (h : S7Kani2BasisLoop.iterate (S7Kani2BasisLoop.step ops.op7 node n)
      fuel iter.start basis=ok out) :
    verifier.accumulate_batched_with_node_loop0_loop0 ops iter node basis n=ok out := by
  induction fuel generalizing iter basis with
  | zero =>
    have same : basis=out := Result.ok.inj h
    subst out
    obtain ⟨⟨o,iter1⟩,run,ho,_⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b; rfl)
        iter (by rw [ending]; omega))
    subst o
    unfold verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,verifier.accumulate_batched_with_node_loop0_loop0.body,run,bind_tc_ok]
  | succ fuel ih =>
    unfold S7Kani2BasisLoop.iterate at h
    obtain ⟨basis1,hstep,h⟩ := bind_success _ _ _ h
    obtain ⟨j1,hinc,hj1⟩ := S7Kani2AccumulatorLoop.increment iter.start (by omega)
    rw [hinc,bind_tc_ok] at h
    obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro a b; rfl)
        iter (by rw [ending]; omega))
    subst o
    have index : iter1.start=j1 := UScalar.eq_of_val_eq (by omega)
    have tail := ih iter1 basis1 (he.trans ending) (by omega) (by rw [index]; exact h)
    have step := body ops node n basis iter iter1 iter.start (by omega) run
    rw [hstep,bind_tc_ok] at step
    unfold verifier.accumulate_batched_with_node_loop0_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,step]
    exact tail

#print axioms body
#print axioms from_iterate
end AspisR1.Port4C_BasisInner
end

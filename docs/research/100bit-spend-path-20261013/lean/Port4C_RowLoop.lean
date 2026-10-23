import Port4C_RowStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_RowLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeQueryBody
open Port3_RowsInstall (toK toBW fromBW toWeights)
open Port3_PushFrame (bind_success)
abbrev K := aspis_core.field.QM31
abbrev BW := verifier.BatchedWeights
abbrev cell := S7JoinBasisBlock.cell

private theorem basis_read (basis : Array U32 256#usize) (j : Usize) (hj : j.val<64) :
    Array.index_usize basis j=ok (cell basis j.val) := by
  have bound : j.val<basis.val.length := by rw [basis.property]; change j.val<256; omega
  obtain ⟨m,hm,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec basis j bound)
  have same : m=cell basis j.val := by
    simp only [cell,S7JoinBasisBlock.cell,List.getElem?_eq_getElem bound,Option.getD_some]
    exact hval
  exact hm.trans (congrArg Result.ok same)

private theorem owned_step (v : alloc.vec.Vec K) (power : K) (next j : Usize)
    (basis : Array U32 256#usize) (b : BW) (pair : S7Kani2AccumulatorLoop.State)
    (hj : j.val<64)
    (h : S7Kani2AccumulatorLoop.step S7JoinRowsTrace.backend basis (toK power) next
      64#usize j (toWeights v,toBW b)=ok pair) :
    ∃ b1 : BW, pair=(toWeights v,toBW b1) ∧
      Port3_NativeRowFrame.push b j power (cell basis j.val)=ok b1 := by
  unfold S7Kani2AccumulatorLoop.step at h
  rw [basis_read basis j hj,bind_tc_ok] at h
  obtain ⟨b1,hpush,h⟩ := bind_success _ _ _ h
  iterate 8 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  have same := Result.ok.inj h
  refine ⟨fromBW b1,same.symm,?_⟩
  change S7Kani2OwnedPush.push_owned (toBW b) j (toK power) (cell basis j.val)=ok b1 at hpush
  unfold Port3_NativeRowFrame.push
  change (do let out ← S7Kani2OwnedPush.push_owned (toBW b) j (toK power) (cell basis j.val)
             ok (fromBW out))=ok (fromBW b1)
  rw [hpush,bind_tc_ok]

/-- Lower the COMPLETE successful emitted owned row traversal to the CURRENT
native range iterator. Every row uses the same actual push and physical read. -/
theorem from_iterate (ops : Ops) (v : alloc.vec.Vec K) (power : K) (next : Usize)
    (basis : Array U32 256#usize) (iter : core.ops.range.Range Usize)
    (b out : BW) (fuel : Nat) (size : v.val.length=64)
    (span : iter.start.val+fuel=64) (ending : iter.end.val=64)
    (h : S7Kani2AccumulatorLoop.iterate
      (S7Kani2AccumulatorLoop.step S7JoinRowsTrace.backend basis (toK power) next 64#usize)
      fuel iter.start (toWeights v,toBW b)=ok (toWeights v,toBW out)) :
    verifier.accumulate_batched_with_node_loop1 (Port4C_RowStd.install ops)
      iter v power next b 64#usize basis=ok out := by
  induction fuel generalizing iter b with
  | zero =>
    have same : b=out := by
      have pair := Result.ok.inj h
      have raw := congrArg (fun p : S7Kani2AccumulatorLoop.State => p.2.raw) pair
      have terms := congrArg (fun p : S7Kani2AccumulatorLoop.State => p.2.terms) pair
      cases b; cases out
      cases raw; cases terms; rfl
    subst out
    unfold verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry]
    rw [Port3_NativeRowLoop.stopped _ _ _ _ _ _ _ _ (by omega)]
  | succ fuel ih =>
    have hj : iter.start.val<64 := by omega
    unfold S7Kani2AccumulatorLoop.iterate at h
    obtain ⟨pair,hstep,h⟩ := bind_success _ _ _ h
    obtain ⟨b1,same,hpush⟩ := owned_step v power next iter.start basis b pair hj hstep
    subst pair
    obtain ⟨j1,hinc,hj1⟩ := S7Kani2AccumulatorLoop.increment iter.start (by omega)
    rw [hinc,bind_tc_ok] at h
    obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro a b; rfl)
        iter (by omega))
    subst o
    have index : iter1.start=j1 := UScalar.eq_of_val_eq (by omega)
    have tail := ih iter1 b1 (by omega) (by rw [he]; exact ending)
      (by rw [index]; exact h)
    obtain ⟨q,hq,_⟩ := WP.spec_imp_exists
      (Slice.index_usize_spec v.deref iter.start (by change iter.start.val<v.val.length; omega))
    have step := Port4C_RowStd.step ops v power next 64#usize basis iter iter1 b b1 iter.start
      (cell basis iter.start.val) q run (basis_read basis iter.start hj) hq hpush
    unfold verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,step]
    exact tail

#print axioms basis_read
#print axioms owned_step
#print axioms from_iterate
end AspisR1.Port4C_RowLoop
end

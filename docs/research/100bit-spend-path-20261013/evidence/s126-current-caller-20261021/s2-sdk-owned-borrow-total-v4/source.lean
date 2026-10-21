import S2SdkOwnedPrimitivesTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.BorrowTotal

/-- The actual shared-borrow guard implies signed checked increment cannot
fail or return None, including the isize::MAX-1 boundary. -/
theorem shared_increment_total (counter : Isize)
    (allowed : shared_allowed counter=ok true) :
    ∃ next : Isize, (counter+1#isize : Result Isize)=ok next ∧
      Isize.checked_add counter 1#isize=some next ∧ next.val=counter.val+1 := by
  have bounds := (PrimitivesTotal.shared_allowed_true counter).mp allowed
  have hs : (counter+1#isize : Result Isize) ⦃ next => next.val=counter.val+(1#isize).val ⦄ := by
    apply IScalar.add_spec <;> scalar_tac
  obtain ⟨next,hnext,hvalue⟩ := spec_imp_exists hs
  refine ⟨next,hnext,?_,by simpa using hvalue⟩
  unfold Isize.checked_add core.num.checked_add_IScalar
  rw [hnext]
  rfl

/-- TOTAL exact read/update pair of the emitted heap operations at a valid slot.
This names the unchanged Vec setter rather than normalizing any account bytes. -/
theorem cell_operations_total (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) :
    ∃ cell : OwnedDataCell, cell=sdk.data_cells.val[slot.val] ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        sdk.data_cells slot=ok cell ∧
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        sdk.data_cells slot=ok (cell,alloc.vec.Vec.set sdk.data_cells slot) := by
  obtain ⟨cell,hread,hcell⟩ := spec_imp_exists
    (alloc.vec.Vec.index_usize_spec sdk.data_cells slot valid)
  obtain ⟨pair,hmut,hpair⟩ := spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec sdk.data_cells slot valid)
  rcases pair with ⟨other,back⟩
  rcases hpair with ⟨hother,hback⟩
  have same : other=cell := hother.trans hcell.symm
  subst other
  subst back
  refine ⟨cell,hcell,?_,?_⟩
  · rw [alloc.vec.Vec.index_slice_index]
    exact hread
  · rw [alloc.vec.Vec.index_mut_slice_index]
    simpa only [hcell] using hmut

/-- TOTAL exact temporary SDK length reference at every valid slot and signed
borrow count. Its successful and rejecting outcomes follow the actual guard. -/
theorem data_len_total (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) :
    ∃ cell : OwnedDataCell, cell=sdk.data_cells.val[slot.val] ∧
      owned_data_len sdk slot=ok
        (if cell.borrowed≥0#isize ∧ cell.borrowed<core.num.Isize.MAX
         then core.result.Result.Ok (alloc.vec.Vec.len cell.bytes)
         else core.result.Result.Err solana_program_error.ProgramError.AccountBorrowFailed) := by
  obtain ⟨cell,hcell,hread,_⟩ := cell_operations_total sdk slot valid
  refine ⟨cell,hcell,?_⟩
  by_cases allowed : cell.borrowed≥0#isize ∧ cell.borrowed<core.num.Isize.MAX
  · have hb : shared_allowed cell.borrowed=ok true := by
      rw [PrimitivesTotal.shared_allowed_exact]
      simp only [allowed,decide_true]
    simp only [owned_data_len,hread,bind_tc_ok,hb,if_pos allowed]
  · have hb : shared_allowed cell.borrowed=ok false := by
      rw [PrimitivesTotal.shared_allowed_exact]
      simp only [allowed,decide_false]
    simp only [owned_data_len,hread,bind_tc_ok,hb,if_neg allowed]

#print axioms cell_operations_total
#print axioms data_len_total
#print axioms shared_increment_total
end AspisS2OwnedStage1.SdkReference.BorrowTotal

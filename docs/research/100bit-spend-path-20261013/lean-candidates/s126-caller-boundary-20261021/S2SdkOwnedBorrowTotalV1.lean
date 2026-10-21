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

/-- The SDK shared-guard release decrements a strictly positive signed count.
The full signed checked-sub operation is total under precisely that condition. -/
theorem shared_decrement_total (counter : Isize) (positive : 0<counter.val) :
    ∃ next : Isize, (counter-1#isize : Result Isize)=ok next ∧
      Isize.checked_sub counter 1#isize=some next ∧ next.val=counter.val-1 := by
  have hs : (counter-1#isize : Result Isize) ⦃ next => next.val=counter.val-(1#isize).val ⦄ := by
    apply IScalar.sub_spec <;> scalar_tac
  obtain ⟨next,hnext,hvalue⟩ := spec_imp_exists hs
  refine ⟨next,hnext,?_,by simpa using hvalue⟩
  unfold Isize.checked_sub core.num.checked_sub_IScalar
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
      simp only [allowed,and_self,decide_true]
    simp only [owned_data_len,hread,bind_tc_ok,hb,if_pos allowed]
    rfl
  · have hb : shared_allowed cell.borrowed=ok false := by
      rw [PrimitivesTotal.shared_allowed_exact]
      simp only [allowed,decide_false]
    simp only [owned_data_len,hread,bind_tc_ok,hb,if_neg allowed]
    rfl

/-- TOTAL exact checkpoint acquisition at a valid heap slot. The only modified
field is its signed counter; bytes and all SDK metadata/lamports are retained. -/
theorem checkpoint_acquire_total (sdk : OwnedSdk) (guards : LiveGuards) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) :
    ∃ cell : OwnedDataCell, cell=sdk.data_cells.val[slot.val] ∧
      owned_acquire_checkpoint sdk guards slot=ok
        (if cell.borrowed != 0#isize
         then (core.result.Result.Err solana_program_error.ProgramError.AccountBorrowFailed,sdk,guards)
         else (core.result.Result.Ok (),
           {sdk with data_cells:=alloc.vec.Vec.set sdk.data_cells slot {cell with borrowed:=(-1)#isize}},
           {guards with checkpoint:=some slot})) := by
  obtain ⟨cell,hcell,hread,hmut⟩ := cell_operations_total sdk slot valid
  refine ⟨cell,hcell,?_⟩
  simp only [owned_acquire_checkpoint,hread,bind_tc_ok]
  split
  · rfl
  · rw [hmut]
    rfl

/-- TOTAL shared acquisition at a valid slot, with exact failure and the full
successful counter/heap frame. No byte snapshot or child-success is assumed. -/
theorem shared_acquire_total (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) :
    ∃ (cell : OwnedDataCell) (result : core.result.Result Unit solana_program_error.ProgramError)
      (sdkOut : OwnedSdk),
      cell=sdk.data_cells.val[slot.val] ∧
      owned_acquire_shared sdk slot=ok (result,sdkOut) ∧
      ((result=core.result.Result.Err solana_program_error.ProgramError.AccountBorrowFailed ∧
        sdkOut=sdk ∧ ¬(cell.borrowed≥0#isize ∧ cell.borrowed<core.num.Isize.MAX)) ∨
       ∃ next : Isize,
        result=core.result.Result.Ok () ∧
        cell.borrowed≥0#isize ∧ cell.borrowed<core.num.Isize.MAX ∧
        next.val=cell.borrowed.val+1 ∧
        sdkOut={sdk with data_cells:=alloc.vec.Vec.set sdk.data_cells slot {cell with borrowed:=next}}) := by
  obtain ⟨cell,hcell,hread,hmut⟩ := cell_operations_total sdk slot valid
  by_cases allowed : cell.borrowed≥0#isize ∧ cell.borrowed<core.num.Isize.MAX
  · have hb := (PrimitivesTotal.shared_allowed_true cell.borrowed).mpr allowed
    obtain ⟨next,_,hchecked,hvalue⟩ := shared_increment_total cell.borrowed hb
    refine ⟨cell,.Ok (),
      {sdk with data_cells:=alloc.vec.Vec.set sdk.data_cells slot {cell with borrowed:=next}},
      hcell,?_,Or.inr ⟨next,rfl,allowed.1,allowed.2,hvalue,rfl⟩⟩
    simp only [owned_acquire_shared,hread,bind_tc_ok,hb,hchecked,hmut,
      core.option.Option.unwrap]
    rfl
  · have hb : shared_allowed cell.borrowed=ok false := by
      rw [PrimitivesTotal.shared_allowed_exact]
      simp only [allowed,decide_false]
    refine ⟨cell,.Err solana_program_error.ProgramError.AccountBorrowFailed,sdk,
      hcell,?_,Or.inl ⟨rfl,rfl,allowed⟩⟩
    simp only [owned_acquire_shared,hread,bind_tc_ok,hb]
    rfl

#print axioms shared_decrement_total
#print axioms checkpoint_acquire_total
#print axioms shared_acquire_total
#print axioms cell_operations_total
#print axioms data_len_total
#print axioms shared_increment_total
end AspisS2OwnedStage1.SdkReference.BorrowTotal

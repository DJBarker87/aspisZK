import S2SdkCopyArrayLawsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace AspisS2OwnedStage1.SdkReference.CopyLoop

/-- TOTAL count induction for the actual emitted loop. Its invariant retains
the entire initial SDK and changes only the selected byte vector. -/
theorem copy_loop_total (sdk : OwnedSdk) (slot : Usize) (source : Slice U8)
    (cell : OwnedDataCell) (valid : slot.val<sdk.data_cells.val.length)
    (actual : cell=sdk.data_cells.val[slot.val])
    (sameLength : cell.bytes.val.length=source.val.length) :
    copy_in_place_loop sdk slot source 0#usize=ok (replaceBytes sdk slot cell source) := by
  let inv : (OwnedSdk × Usize) → Prop := fun state =>
    ∃ bytes : alloc.vec.Vec U8,
      state.1=replaceBytes sdk slot cell bytes ∧ bytes.val.length=source.val.length ∧
      state.2.val≤source.val.length ∧ PrefixEq bytes source state.2.val
  have run : WP.spec (copy_in_place_loop sdk slot source 0#usize)
      (fun output => output=replaceBytes sdk slot cell source) := by
    unfold copy_in_place_loop
    refine loop.spec_decr_nat (fun state : OwnedSdk × Usize => source.val.length-state.2.val)
      inv (fun output => output=replaceBytes sdk slot cell source)
      (fun (heap,offset) => copy_in_place_loop.body slot source heap offset)
      (sdk,0#usize) ?_ ?_
    · intro state held
      rcases state with ⟨heap,offset⟩
      rcases held with ⟨bytes,heapEq,length,ordered,copied⟩
      dsimp only at heapEq ordered copied ⊢
      subst heap
      by_cases range : offset.val<source.val.length
      · have currentValid : slot.val<
            (replaceBytes sdk slot cell bytes).data_cells.val.length := by
          simpa only [replace_length] using valid
        have currentCell := replace_cell sdk slot cell bytes valid
        have targetRange : offset.val<
            ((replaceBytes sdk slot cell bytes).data_cells.val[slot.val]).bytes.val.length := by
          rw [currentCell]
          omega
        obtain ⟨row,byte,hrow,hbyte,hstep⟩ := copy_step_total
          (replaceBytes sdk slot cell bytes) slot source offset currentValid range targetRange
        have rowEq : row={cell with bytes:=bytes} := hrow.trans currentCell
        subst row
        rw [replace_twice] at hstep
        obtain ⟨next,hadd,nextValue⟩ := increment_total offset source range
        have condition : offset<Slice.len source := range
        have body : copy_in_place_loop.body slot source
            (replaceBytes sdk slot cell bytes) offset=ok
            (cont (replaceBytes sdk slot cell (alloc.vec.Vec.set bytes offset byte),next)) := by
          simp only [copy_in_place_loop.body,if_pos condition,hstep,hadd,bind_tc_ok]
        rw [body,WP.spec_ok]
        constructor
        · refine ⟨alloc.vec.Vec.set bytes offset byte,rfl,?_,?_,?_⟩
          · simpa [alloc.vec.Vec.set] using length
          · omega
          · rw [nextValue]
            exact prefix_step bytes source offset length range copied byte hbyte
        · omega
      · have condition : ¬offset<Slice.len source := range
        have last : offset.val=source.val.length := by omega
        have allCopied : PrefixEq bytes source source.val.length := by simpa only [last] using copied
        have bytesEq := prefix_complete bytes source length allCopied
        simp only [copy_in_place_loop.body,if_neg condition,WP.spec_ok]
        exact congrArg (replaceBytes sdk slot cell) bytesEq
    · refine ⟨cell.bytes,(replace_same sdk slot cell valid actual).symm,sameLength,?_,?_⟩
      · change (0:Nat)≤source.val.length
        omega
      · intro j impossible
        change j<(0:Nat) at impossible
        omega
  obtain ⟨out,execution,result⟩ := spec_imp_exists run
  simpa only [result] using execution

/-- TOTAL complete reference operation at every valid SDK slot, including
length rejection. All indexing/addition/loop premises are discharged. -/
theorem copy_in_place_total (sdk : OwnedSdk) (slot : Usize) (source : Slice U8)
    (valid : slot.val<sdk.data_cells.val.length) :
    ∃ cell : OwnedDataCell, cell=sdk.data_cells.val[slot.val] ∧
      copy_in_place sdk slot source=ok
        (if cell.bytes.val.length=source.val.length
         then (core.result.Result.Ok (),replaceBytes sdk slot cell source)
         else (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData,sdk)) := by
  obtain ⟨cell,actual,read,_⟩ := BorrowTotal.cell_operations_total sdk slot valid
  refine ⟨cell,actual,?_⟩
  by_cases sameLength : cell.bytes.val.length=source.val.length
  · have same : alloc.vec.Vec.len cell.bytes=Slice.len source := UScalar.eq_of_val_eq sameLength
    have loopDone := copy_loop_total sdk slot source cell valid actual sameLength
    simp only [copy_in_place,read,bind_tc_ok,same,bne_self_eq_false,Bool.false_eq_true,
      if_false,loopDone,if_pos sameLength]
  · have different : alloc.vec.Vec.len cell.bytes≠Slice.len source := by
      intro h
      exact sameLength (congrArg (fun value : Usize => value.val) h)
    have mismatch : (alloc.vec.Vec.len cell.bytes != Slice.len source)=true := bne_iff_ne.mpr different
    simp only [copy_in_place,read,bind_tc_ok,mismatch,if_true,if_neg sameLength]

#print axioms copy_loop_total
#print axioms copy_in_place_total
end AspisS2OwnedStage1.SdkReference.CopyLoop

import S2SdkCopyLoopModelV1
import S2SdkOwnedGuardFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.CopyLoop

/-- Complete SDK update: every account/lamport field and every other data row
is retained, and only the selected cell's byte vector is replaced. -/
def replaceBytes (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell)
    (bytes : alloc.vec.Vec U8) : OwnedSdk :=
  {sdk with data_cells:=alloc.vec.Vec.set sdk.data_cells slot {cell with bytes:=bytes}}

/-- TOTAL emitted one-byte assignment at the actual source index ranges.
Neither read success nor mutable-index/setter success is supplied separately. -/
theorem copy_step_total (sdk : OwnedSdk) (slot : Usize) (source : Slice U8)
    (offset : Usize) (valid : slot.val<sdk.data_cells.val.length)
    (sourceRange : offset.val<source.val.length)
    (targetRange : offset.val<(sdk.data_cells.val[slot.val]).bytes.val.length) :
    ∃ (cell : OwnedDataCell) (byte : U8),
      cell=sdk.data_cells.val[slot.val] ∧ byte=source.val[offset.val] ∧
      copy_step sdk slot source offset=ok
        (replaceBytes sdk slot cell (alloc.vec.Vec.set cell.bytes offset byte)) := by
  obtain ⟨cell,hcell,_,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have target : offset.val<cell.bytes.val.length := by simpa only [hcell] using targetRange
  obtain ⟨byte,hsource,hbyte⟩ := spec_imp_exists
    (alloc.vec.Vec.index_usize_spec source offset sourceRange)
  change Slice.index_usize source offset=ok byte at hsource
  obtain ⟨pair,hmutByte,hpair⟩ := spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec cell.bytes offset target)
  rcases pair with ⟨oldByte,back⟩
  rcases hpair with ⟨_,hback⟩
  subst back
  have selected : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U8)
      cell.bytes offset=ok (oldByte,alloc.vec.Vec.set cell.bytes offset) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmutByte
  refine ⟨cell,byte,hcell,hbyte,?_⟩
  simp only [copy_step,hsource,hmut,selected,bind_tc_ok,Aeneas.Std.uncurry,replaceBytes]

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Every returned byte-step establishes its own counter/guard frame from the
actual reached setter. No independent invariant-transport or slot premise. -/
theorem copy_step_preserves_guards (sdk sdkOut : OwnedSdk) (slot : Usize)
    (source : Slice U8) (offset : Usize) (guards : LiveGuards)
    (held : GuardRelease.LiveInvariant sdk guards)
    (step : copy_step sdk slot source offset=ok sdkOut) :
    GuardRelease.LiveInvariant sdkOut guards := by
  unfold copy_step at step
  obtain ⟨byte,_,step⟩ := bind_success _ _ _ step
  obtain ⟨pair,hmut,step⟩ := bind_success _ _ _ step
  rcases pair with ⟨cell,back⟩
  obtain ⟨pair,_,step⟩ := bind_success _ _ _ step
  rcases pair with ⟨oldByte,backByte⟩
  cases step
  exact GuardFrame.write_bytes_invariant sdk guards slot cell back
    (backByte byte) held hmut

#print axioms copy_step_total
#print axioms copy_step_preserves_guards
end AspisS2OwnedStage1.SdkReference.CopyLoop

import S2SdkOwnedGuardAcquireV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.GuardFrame
open GuardRelease GuardAcquire

/-- Inversion of the actual library mutable-index operation, retaining its
complete setter. Successful indexing derives its own range and exact old row. -/
theorem index_mut_success (sdk : OwnedSdk) (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell)
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back)) :
    ∃ valid : slot.val<sdk.data_cells.val.length,
      old=sdk.data_cells.val[slot.val] ∧ back=alloc.vec.Vec.set sdk.data_cells slot := by
  rw [alloc.vec.Vec.index_mut_slice_index] at h
  unfold alloc.vec.Vec.index_mut_usize at h
  cases read : alloc.vec.Vec.index_usize sdk.data_cells slot with
  | fail error => rw [read] at h; cases h
  | div => rw [read] at h; cases h
  | ok cell =>
    have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        sdk.data_cells slot=ok cell := by
      rw [alloc.vec.Vec.index_slice_index]
      exact read
    have valid := index_success_valid sdk.data_cells slot cell hr
    obtain ⟨expected,hcell,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
    rw [read] at h
    have eq := Prod.mk.inj (Result.ok.inj h)
    have cellEq : cell=expected := Result.ok.inj (hr.symm.trans hread)
    exact ⟨valid,eq.1.symm.trans (cellEq.trans hcell),eq.2.symm⟩

def SameCounters (before after : OwnedSdk) : Prop :=
  after.data_cells.val.length=before.data_cells.val.length ∧
    ∀ index, countAt after index=countAt before index

theorem invariant_transport (before after : OwnedSdk) (guards : LiveGuards)
    (held : LiveInvariant before guards) (same : SameCounters before after) :
    LiveInvariant after guards := by
  rcases same with ⟨length,counters⟩
  simpa only [LiveInvariant,length,counters] using held

/-- The exact checkpoint bytes assignment preserves live guards. Its setter
and old row are derived from the actual reached mutable-index execution; no
independent buffer/counter frame or slot-validity premise is introduced. -/
theorem write_bytes_invariant (sdk : OwnedSdk) (guards : LiveGuards)
    (slot : Usize) (old : OwnedDataCell)
    (back : OwnedDataCell → alloc.vec.Vec OwnedDataCell) (bytes : alloc.vec.Vec U8)
    (held : LiveInvariant sdk guards)
    (h : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot=ok (old,back)) :
    LiveInvariant {sdk with data_cells:=back {old with bytes:=bytes}} guards := by
  obtain ⟨valid,actual,setter⟩ := index_mut_success sdk slot old back h
  subst back
  change LiveInvariant (counterUpdate sdk slot {old with bytes:=bytes} old.borrowed) guards
  apply invariant_transport sdk _ guards held
  refine ⟨update_length _ _ _ _,?_⟩
  intro index
  rw [countAt_update _ _ _ _ valid]
  split
  · rename_i equal
    subst index
    exact (countAt_cell sdk slot valid old actual).symm
  · rfl

#print axioms index_mut_success
#print axioms invariant_transport
#print axioms write_bytes_invariant
end AspisS2OwnedStage1.SdkReference.GuardFrame

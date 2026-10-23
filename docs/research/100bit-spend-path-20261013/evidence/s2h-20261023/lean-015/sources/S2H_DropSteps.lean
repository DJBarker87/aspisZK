import S2H_CheckpointStep
import S2SdkOwnedGuardReleaseV1
import S2D_Cleanup
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2Trust S2E S2E_Reference.S2E_Reference

/-- The guards removed from the trusted heap are deliberately not inferred
from the counter-only SDK carrier. The caller supplies its actual live token. -/
theorem image_release {Child Alloc Event : Type} (m : AllocationMap)
    (h : Heap (World Child Alloc Event)) (sdk : SDK) (image : HeapImage m h sdk)
    (slot : Usize) (cell : OwnedDataCell) (next : Isize) (g : Guard)
    (read : sdk.data_cells.val[slot.val]? = some cell)
    (cellIdentity : g.cell = m.dataCell slot.val)
    (value : next.val = if g.kind = .shared then h.counter g.cell - 1 else 0) :
    HeapImage m (release h g) (setCounter sdk slot cell next) := by
  have update := image_counter_update m h sdk image slot cell next read
  refine ⟨update.accounts,update.lamports,update.handles,?_,update.slots⟩
  simpa only [release,cellIdentity,← value] using update.data

def dropReference (sdk : SDK) (slot : Usize) (kind : Kind) : Result SDK :=
  match kind with
  | .shared => release_shared sdk slot
  | .exclusive => owned_release_guards sdk {checkpoint:=some slot,«public»:=none,proof:=none}

/-- Exact SDK guard-drop port, arbitrary full buffers and both kinds. The live
counter conditions follow from Valid, rather than being assumed as restored
caller counters. Compiler destruction order and Box/Vec owner drops remain open. -/
theorem guard_sdk_drop {W Child Alloc Event : Type}
    (L : Library W (World Child Alloc Event)) (trust : S2TrustedSdkBorrow L)
    (m : AllocationMap) (n : W) (h : Heap (World Child Alloc Event)) (sdk : SDK)
    (related : L.related n h) (valid : Valid h) (image : HeapImage m h sdk)
    (slot : Usize) (cell : OwnedDataCell) (token : Nat) (g : Guard)
    (read : sdk.data_cells.val[slot.val]? = some cell)
    (live : lookup h token = some g) (cellIdentity : g.cell = m.dataCell slot.val) :
    ∃ out after, dropReference sdk slot g.kind = ok out ∧
      L.run n (.drop token) = (after,.unit) ∧ L.related after (release h g) ∧
      HeapImage m (release h g) out := by
  let cut : S2D.BorrowCut n h L (fun w _ => w) 0 := ⟨h,related,valid⟩
  obtain ⟨after,step,post⟩ := S2D.actual_guard_drop trust cut token g live
  have bounds := (List.getElem?_eq_some_iff.mp read).1
  have actual := (List.getElem?_eq_some_iff.mp read).2.symm
  have counter := (image.data slot.val cell read).2.2.2.1
  have count := SdkReference.GuardRelease.countAt_cell sdk slot bounds cell actual
  cases kind : g.kind with
  | shared =>
    have positive := S2D.shared_drop_counter_positive cut token g live kind
    rw [cellIdentity,counter] at positive
    obtain ⟨row,next,hrow,hnext,ran⟩ := SdkReference.GuardRelease.drop_shared_total sdk slot bounds (by omega)
    have same : row = cell := hrow.trans actual.symm
    subst row
    have value : next.val = if g.kind = .shared then h.counter g.cell - 1 else 0 := by
      rw [kind,if_pos rfl,cellIdentity,counter]
      omega
    refine ⟨setCounter sdk slot cell next,after,?_,step,post,
      image_release m h sdk image slot cell next g read cellIdentity value⟩
    change SdkReference.GuardRelease.dropShared sdk slot = _
    exact ran
  | exclusive =>
    have minus := S2D.exclusive_drop_counter_negative_one cut token g live kind
    rw [cellIdentity,counter] at minus
    obtain ⟨row,hrow,ran⟩ := SdkReference.GuardRelease.drop_checkpoint_total sdk slot bounds (by omega)
    have same : row = cell := hrow.trans actual.symm
    subst row
    have different : g.kind ≠ .shared := by rw [kind]; intro impossible; cases impossible
    have value : (0#isize).val = if g.kind = .shared then h.counter g.cell - 1 else 0 := by
      rw [if_neg different]
      scalar_tac
    refine ⟨setCounter sdk slot cell 0#isize,after,?_,step,post,
      image_release m h sdk image slot cell 0#isize g read cellIdentity value⟩
    change SdkReference.owned_release_guards sdk
      {checkpoint:=some slot,«public»:=none,proof:=none} = _
    rw [SdkReference.GuardRelease.release_eq]
    exact ran

#print axioms image_release
#print axioms guard_sdk_drop
end AspisR1.S2H

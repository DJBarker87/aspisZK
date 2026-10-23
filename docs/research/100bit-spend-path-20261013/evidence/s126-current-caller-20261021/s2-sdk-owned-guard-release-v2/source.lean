import S2SdkOwnedBorrowTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS2OwnedStage1.SdkReference.GuardRelease

/-- Total mathematical counter projection; valid-slot obligations are separate. -/
def countAt (sdk : OwnedSdk) (index : Nat) : Int :=
  (sdk.data_cells.val.map (fun cell => cell.borrowed.val)).getD index 0

def counterUpdate (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell) (next : Isize) : OwnedSdk :=
  {sdk with data_cells:=alloc.vec.Vec.set sdk.data_cells slot {cell with borrowed:=next}}

theorem update_length (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell) (next : Isize) :
    (counterUpdate sdk slot cell next).data_cells.val.length=sdk.data_cells.val.length := by
  simp [counterUpdate,alloc.vec.Vec.set]

theorem countAt_cell (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) (cell : OwnedDataCell)
    (hcell : cell=sdk.data_cells.val[slot.val]) :
    countAt sdk slot.val=cell.borrowed.val := by
  subst cell
  simp [countAt,List.getD_eq_getElem?_getD,valid]

theorem countAt_update (sdk : OwnedSdk) (slot : Usize) (cell : OwnedDataCell) (next : Isize)
    (valid : slot.val<sdk.data_cells.val.length) (index : Nat) :
    countAt (counterUpdate sdk slot cell next) index=
      if slot.val=index then next.val else countAt sdk index := by
  by_cases equal : slot.val=index
  · subst index
    simp [countAt,counterUpdate,alloc.vec.Vec.set,List.getD_eq_getElem?_getD,valid]
  · simp [countAt,counterUpdate,alloc.vec.Vec.set,List.getD_eq_getElem?_getD,List.map_set,
      List.getElem?_set,equal]

/-- These are literal subterms of the emitted release function, exposed only
for composition. `release_eq` checks the complete parent identity. -/
def dropShared (sdk : OwnedSdk) (slot : Usize) : Result OwnedSdk := do
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
  let option ← lift (Isize.checked_sub cell.borrowed 1#isize)
  let next ← core.option.Option.unwrap option
  let (old,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
  ok {sdk with data_cells:=back {old with borrowed:=next}}

def dropCheckpoint (sdk : OwnedSdk) (slot : Usize) : Result OwnedSdk := do
  let cell ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
  let option ← lift (Isize.checked_add cell.borrowed 1#isize)
  let next ← core.option.Option.unwrap option
  let (old,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells slot
  ok {sdk with data_cells:=back {old with borrowed:=next}}

theorem release_eq (sdk : OwnedSdk) (guards : LiveGuards) :
    owned_release_guards sdk guards=(do
      let sdk1 ← match guards.proof with | none => ok sdk | some slot => dropShared sdk slot
      let sdk2 ← match guards.«public» with | none => ok sdk1 | some slot => dropShared sdk1 slot
      match guards.checkpoint with | none => ok sdk2 | some slot => dropCheckpoint sdk2 slot) := rfl

theorem drop_shared_total (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) (positive : 0<countAt sdk slot.val) :
    ∃ (cell : OwnedDataCell) (next : Isize),
      cell=sdk.data_cells.val[slot.val] ∧ next.val=countAt sdk slot.val-1 ∧
      dropShared sdk slot=ok (counterUpdate sdk slot cell next) := by
  obtain ⟨cell,hcell,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have hcount := countAt_cell sdk slot valid cell hcell
  obtain ⟨next,_,hchecked,hvalue⟩ := BorrowTotal.shared_decrement_total cell.borrowed (by omega)
  refine ⟨cell,next,hcell,by omega,?_⟩
  simp only [dropShared,hread,bind_tc_ok,hchecked,core.option.Option.unwrap,hmut]
  rfl

theorem checkpoint_increment :
    Isize.checked_add (-1)#isize 1#isize=some 0#isize := by
  have hs : ((-1)#isize+1#isize : Result Isize) ⦃ next =>
      next.val=((-1)#isize).val+(1#isize).val ⦄ := by
    apply IScalar.add_spec <;> scalar_tac
  obtain ⟨next,hnext,hvalue⟩ := spec_imp_exists hs
  have hz : next=0#isize := by apply IScalar.eq_of_val_eq; scalar_tac
  subst next
  unfold Isize.checked_add core.num.checked_add_IScalar
  rw [hnext]
  rfl

theorem drop_checkpoint_total (sdk : OwnedSdk) (slot : Usize)
    (valid : slot.val<sdk.data_cells.val.length) (exclusive : countAt sdk slot.val = -1) :
    ∃ cell : OwnedDataCell, cell=sdk.data_cells.val[slot.val] ∧
      dropCheckpoint sdk slot=ok (counterUpdate sdk slot cell 0#isize) := by
  obtain ⟨cell,hcell,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have hcount := countAt_cell sdk slot valid cell hcell
  have hc : cell.borrowed=(-1)#isize := by
    apply IScalar.eq_of_val_eq
    scalar_tac
  refine ⟨cell,hcell,?_⟩
  simp only [dropCheckpoint,hread,bind_tc_ok,hc,checkpoint_increment,
    core.option.Option.unwrap,hmut]
  rfl

/-- Logical invariant of the actually live guards. Both shared slots may alias;
when they do, their counter must cover both guards. The exclusive slot cannot
alias either shared slot. This predicate must still be derived from the parent
execution; it is not an independently discharged SDK caller hypothesis. -/
def LiveInvariant (sdk : OwnedSdk) (guards : LiveGuards) : Prop :=
  (∀ slot, guards.checkpoint=some slot →
    slot.val<sdk.data_cells.val.length ∧ countAt sdk slot.val = -1 ∧
    guards.«public»≠some slot ∧ guards.proof≠some slot) ∧
  (∀ slot, guards.«public»=some slot →
    slot.val<sdk.data_cells.val.length ∧
    1+(if guards.proof=some slot then 1 else 0)≤countAt sdk slot.val) ∧
  (∀ slot, guards.proof=some slot →
    slot.val<sdk.data_cells.val.length ∧
    1+(if guards.«public»=some slot then 1 else 0)≤countAt sdk slot.val)

theorem invariant_none (sdk : OwnedSdk) :
    LiveInvariant sdk {checkpoint:=none,«public»:=none,proof:=none} := by
  simp [LiveInvariant]

theorem invariant_drop_proof (sdk : OwnedSdk) (guards : LiveGuards) (slot : Usize)
    (cell : OwnedDataCell) (next : Isize) (held : LiveInvariant sdk guards)
    (which : guards.proof=some slot) (value : next.val=countAt sdk slot.val-1) :
    LiveInvariant (counterUpdate sdk slot cell next) {guards with proof:=none} := by
  rcases held with ⟨checkpoint,publicHeld,proofHeld⟩
  have valid := (proofHeld slot which).1
  refine ⟨?_,?_,?_⟩
  · intro other hother
    rcases checkpoint other hother with ⟨hv,hc,hp,hq⟩
    have different : slot.val≠other.val := by
      intro equal
      have hs : slot=other := UScalar.eq_of_val_eq equal
      subst other
      exact hq which
    refine ⟨by simpa only [update_length] using hv,?_,hp,by simp⟩
    rw [countAt_update _ _ _ _ valid,if_neg different]
    exact hc
  · intro other hother
    rcases publicHeld other hother with ⟨hv,hc⟩
    refine ⟨by simpa only [update_length] using hv,?_⟩
    change (1:Int)≤countAt (counterUpdate sdk slot cell next) other.val
    by_cases equal : slot=other
    · subst other
      rw [countAt_update _ _ _ _ valid,if_pos rfl]
      simp only [which,if_pos rfl] at hc
      omega
    · have different : slot.val≠other.val := by
        intro hv
        exact equal (UScalar.eq_of_val_eq hv)
      have neq : guards.proof≠some other := by
        rw [which]
        exact fun h => equal (Option.some.inj h)
      rw [countAt_update _ _ _ _ valid,if_neg different]
      simp only [if_neg neq,add_zero] at hc
      exact hc
  · intro other hother
    cases hother

#print axioms checkpoint_increment
#print axioms drop_checkpoint_total
#print axioms invariant_none
#print axioms invariant_drop_proof
#print axioms update_length
#print axioms countAt_cell
#print axioms countAt_update
#print axioms release_eq
#print axioms drop_shared_total
end AspisS2OwnedStage1.SdkReference.GuardRelease

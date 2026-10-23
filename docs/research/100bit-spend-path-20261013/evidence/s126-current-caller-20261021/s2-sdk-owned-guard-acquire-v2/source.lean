import S2SdkOwnedGuardReleaseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.GuardAcquire
open GuardRelease

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m; f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Reached source read success derives slot validity; it is not supplied as
an unrelated range premise to the parent acquisition theorem. -/
theorem index_success_valid {T : Type} (bytes : alloc.vec.Vec T) (index : Usize) (value : T)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) bytes index=ok value) :
    index.val<bytes.val.length := by
  cases read : bytes.val[index.val]? with
  | none =>
    simp [alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize,read] at h
  | some other =>
    obtain ⟨valid,_⟩ := List.getElem?_eq_some_iff.mp read
    exact valid

abbrev noGuards : LiveGuards := {checkpoint:=none,«public»:=none,proof:=none}

/-- Every ordinary return of the first actual checkpoint acquisition produces
the release invariant, including its BorrowFailed return. Public/proof guards
remain absent. Slot validity is derived from the same reached read. -/
theorem checkpoint_acquire_invariant (sdk sdkOut : OwnedSdk) (slot : Usize)
    (result : core.result.Result Unit solana_program_error.ProgramError) (guardsOut : LiveGuards)
    (h : owned_acquire_checkpoint sdk noGuards slot=ok (result,sdkOut,guardsOut)) :
    LiveInvariant sdkOut guardsOut ∧ guardsOut.«public»=none ∧ guardsOut.proof=none := by
  unfold owned_acquire_checkpoint at h
  obtain ⟨first,hfirst,h⟩ := bind_success _ _ _ h
  have valid := index_success_valid sdk.data_cells slot first hfirst
  obtain ⟨cell,hcell,hread,hmut⟩ := BorrowTotal.cell_operations_total sdk slot valid
  have same : first=cell := Result.ok.inj (hfirst.symm.trans hread)
  subst first
  split at h
  · cases h
    exact ⟨invariant_none sdk,rfl,rfl⟩
  · rw [hmut] at h
    simp only [bind_tc_ok] at h
    cases h
    refine ⟨?_,rfl,rfl⟩
    change LiveInvariant (counterUpdate sdk slot cell (-1)#isize)
      {checkpoint:=some slot,«public»:=none,proof:=none}
    refine ⟨?_,?_,?_⟩
    · intro other which
      have equal : slot=other := Option.some.inj which
      subst other
      refine ⟨by simpa only [update_length] using valid,?_,by simp,by simp⟩
      rw [countAt_update _ _ _ _ valid,if_pos rfl]
      scalar_tac
    · intro other which
      cases which
    · intro other which
      cases which

/-- Add one shared guard to the concrete counter heap. Existing public/proof
aliasing is handled by the multiplicity bound, not excluded as a premise. -/
theorem invariant_add_proof (sdk : OwnedSdk) (guards : LiveGuards) (slot : Usize)
    (cell : OwnedDataCell) (next : Isize) (held : LiveInvariant sdk guards)
    (fresh : guards.proof=none) (valid : slot.val<sdk.data_cells.val.length)
    (actual : cell=sdk.data_cells.val[slot.val]) (nonnegative : 0≤cell.borrowed.val)
    (value : next.val=cell.borrowed.val+1) :
    LiveInvariant (counterUpdate sdk slot cell next) {guards with proof:=some slot} := by
  rcases held with ⟨checkpoint,publicHeld,proofHeld⟩
  have hcount := countAt_cell sdk slot valid cell actual
  refine ⟨?_,?_,?_⟩
  · intro other hother
    rcases checkpoint other hother with ⟨hv,hc,hp,_⟩
    have unequal : slot≠other := by
      intro equal
      subst other
      omega
    have different : slot.val≠other.val := fun h => unequal (UScalar.eq_of_val_eq h)
    refine ⟨by simpa only [update_length] using hv,?_,hp,?_⟩
    · rw [countAt_update _ _ _ _ valid,if_neg different]
      exact hc
    · exact fun h => unequal (Option.some.inj h)
  · intro other hother
    rcases publicHeld other hother with ⟨hv,hc⟩
    have lower : (1:Int)≤countAt sdk other.val := by simpa [fresh] using hc
    refine ⟨by simpa only [update_length] using hv,?_⟩
    change 1+(if (some slot : Option Usize)=some other then 1 else 0)≤
      countAt (counterUpdate sdk slot cell next) other.val
    by_cases equal : slot=other
    · subst other
      rw [countAt_update _ _ _ _ valid,if_pos rfl]
      norm_num only [if_pos rfl]
      omega
    · have different : slot.val≠other.val := fun h => equal (UScalar.eq_of_val_eq h)
      have ne : (some slot : Option Usize)≠some other := fun h => equal (Option.some.inj h)
      rw [if_neg ne,countAt_update _ _ _ _ valid,if_neg different]
      simpa only [add_zero] using lower
  · intro other hother
    have equal : slot=other := Option.some.inj hother
    subst other
    refine ⟨by simpa only [update_length] using valid,?_⟩
    rw [countAt_update _ _ _ _ valid,if_pos rfl]
    by_cases present : guards.«public»=some slot
    · have lower : (1:Int)≤countAt sdk slot.val := by
        have hh := (publicHeld slot present).2
        simpa [fresh] using hh
      norm_num only [if_pos present]
      omega
    · rw [if_neg present]
      norm_num only
      omega

theorem invariant_add_public (sdk : OwnedSdk) (guards : LiveGuards) (slot : Usize)
    (cell : OwnedDataCell) (next : Isize) (held : LiveInvariant sdk guards)
    (fresh : guards.«public»=none) (valid : slot.val<sdk.data_cells.val.length)
    (actual : cell=sdk.data_cells.val[slot.val]) (nonnegative : 0≤cell.borrowed.val)
    (value : next.val=cell.borrowed.val+1) :
    LiveInvariant (counterUpdate sdk slot cell next) {guards with «public»:=some slot} := by
  have first := invariant_add_proof sdk (swapShared guards) slot cell next
    (invariant_swap sdk guards held) fresh valid actual nonnegative value
  exact invariant_swap (counterUpdate sdk slot cell next)
    {swapShared guards with proof:=some slot} first

#print axioms invariant_add_proof
#print axioms invariant_add_public
#print axioms index_success_valid
#print axioms checkpoint_acquire_invariant
end AspisS2OwnedStage1.SdkReference.GuardAcquire

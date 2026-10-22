import S2SdkReadyAcquireV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.ReadyState

/-- The existing full owned SDK types, with three ordinary cells. Byte vectors,
all counter/Rc fields and account/lamport metadata remain arbitrary values. -/
def triple {T : Type} (a b c : T) : alloc.vec.Vec T :=
  ⟨[a,b,c],by scalar_tac⟩

def state (accounts : alloc.vec.Vec OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (proof public checkpoint : OwnedDataCell) : OwnedSdk :=
  {accounts:=accounts,data_cells:=triple proof public checkpoint,lamports_cells:=lamports}

theorem read_zero {T : Type} (a b c : T) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) (triple a b c) 0#usize=ok a := by
  simp [triple,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize]

theorem read_one {T : Type} (a b c : T) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) (triple a b c) 1#usize=ok b := by
  simp [triple,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize]

theorem read_two {T : Type} (a b c : T) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) (triple a b c) 2#usize=ok c := by
  simp [triple,alloc.vec.Vec.index_slice_index,alloc.vec.Vec.index_usize]

/-- First actual acquisition, with its exact complete SDK result constructed.
No success premise, independent state-effect premise or byte clone is used. -/
theorem checkpoint (accounts : alloc.vec.Vec OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell)
    (guards : LiveGuards) (zero : c.borrowed=0#isize) :
    owned_acquire_checkpoint (state accounts lamports p u c) guards 2#usize=
      ok (.Ok (),state accounts lamports p u {c with borrowed:=(-1)#isize},
        {guards with checkpoint:=some 2#usize}) := by
  have step := ReadyAcquire.checkpoint_success (state accounts lamports p u c) guards
    2#usize c (read_two p u c) zero
  simpa [GuardRelease.counterUpdate,state,triple,alloc.vec.Vec.set] using step

/-- The public acquisition is constructed at its actual slot. It may be used
only at its source site after scanning; this does not reorder native errors. -/
theorem public_acquire (accounts : alloc.vec.Vec OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell)
    (allowed : shared_allowed u.borrowed=ok true) :
    ∃ next : Isize, next.val=u.borrowed.val+1 ∧
      owned_acquire_shared (state accounts lamports p u c) 1#usize=
        ok (.Ok (),state accounts lamports p {u with borrowed:=next} c) := by
  obtain ⟨next,value,step⟩ := ReadyAcquire.shared_success
    (state accounts lamports p u c) 1#usize u (read_one p u c) allowed
  refine ⟨next,value,?_⟩
  simpa [GuardRelease.counterUpdate,state,triple,alloc.vec.Vec.set] using step

/-- The proof acquisition at its actual slot, to be used after the same
source decode, validation and encoding. No enclosing success is assumed. -/
theorem proof_acquire (accounts : alloc.vec.Vec OwnedAccount)
    (lamports : alloc.vec.Vec OwnedLamportsCell) (p u c : OwnedDataCell)
    (allowed : shared_allowed p.borrowed=ok true) :
    ∃ next : Isize, next.val=p.borrowed.val+1 ∧
      owned_acquire_shared (state accounts lamports p u c) 0#usize=
        ok (.Ok (),state accounts lamports {p with borrowed:=next} u c) := by
  obtain ⟨next,value,step⟩ := ReadyAcquire.shared_success
    (state accounts lamports p u c) 0#usize p (read_zero p u c) allowed
  refine ⟨next,value,?_⟩
  simpa [GuardRelease.counterUpdate,state,triple,alloc.vec.Vec.set] using step

#print axioms checkpoint
#print axioms public_acquire
#print axioms proof_acquire
#print axioms read_zero
#print axioms read_one
#print axioms read_two
end AspisS2OwnedStage1.SdkReference.ReadyState

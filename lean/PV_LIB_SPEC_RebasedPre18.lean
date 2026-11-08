import PV_LIB_SPEC_RebasedEntry18
import PV_LIB_SPEC_SuccessSchedule12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_RebasedPre18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner PV_OWN2_Codec
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen PV_LIB_SPEC_RebasedEntry18
open PV_LIB_SPEC_RebasedEntry18 (store slot)
open PV_LIB_SPEC_RebasedCaptures18 (places captures closure site zero one runHeader nHeader)

/-- Native initial state does not erase the entry's captured bytes. -/
theorem memory_before (a : Nat) (bound : a<16384) :
    state.world.memory a = PV_LIB_SPEC_RebasedCaptures18.state.world.memory a :=
  PV_LIB_SPEC_RebasedEntry18.memory_before a bound

theorem receivers :
    receiver state places.run = some (0,PV_LIB_SPEC_RebasedCaptures18.runHeader) ∧
    receiver state places.n = some (1,PV_LIB_SPEC_RebasedCaptures18.nHeader) ∧
    receiver state places.f = some (2,PV_LIB_SPEC_RebasedCaptures18.fHeader) ∧
    receiver state places.handles = some (3,PV_LIB_SPEC_RebasedCaptures18.taskHeader) :=
  PV_LIB_SPEC_RebasedCaptures18.receivers

theorem run_bytes : PV_STX_OriginalCopyTyped.bytesAt state.world.memory 4208 16 0 =
    PV_STX_OriginalCopyTyped.bytesAt PV_LIB_SPEC_RebasedCaptures18.state.world.memory 4208 16 0 := by
  funext i
  exact memory_before _ (by have := i.isLt; omega)

theorem n_bytes : PV_STX_OriginalCopyTyped.bytesAt state.world.memory 4160 8 0 =
    PV_STX_OriginalCopyTyped.bytesAt PV_LIB_SPEC_RebasedCaptures18.state.world.memory 4160 8 0 := by
  funext i
  exact memory_before _ (by have := i.isLt; omega)

theorem run_typed : TypedMemory 16 decodeFatPointer state
    ⟨places.run,[PV_OWN2_RunBorrowAddress.runWords site zero zero]⟩ := by
  constructor
  · refine ⟨0,runHeader,receivers.1,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    decide
  · intro id h selected
    change receiver state places.run = some (id,h) at selected
    rw [receivers.1] at selected
    cases selected
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i=0 := by simpa using bound
    subst i
    change decodeFatPointer (PV_STX_OriginalCopyTyped.bytesAt state.world.memory 4208 16 0) = _
    rw [run_bytes,PV_LIB_SPEC_RebasedCaptures18.run_bytes]
    exact PV_OWN2_OperandImages.decode_pairBytes _ _

theorem n_typed : UsizeMemory state ⟨places.n,[one]⟩ := by
  constructor
  · refine ⟨1,nHeader,receivers.2.1,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    decide
  · intro id h selected
    change receiver state places.n = some (id,h) at selected
    rw [receivers.2.1] at selected
    cases selected
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i=0 := by simpa using bound
    subst i
    change decodePointer (PV_STX_OriginalCopyTyped.bytesAt state.world.memory 4160 8 0) = some one
    rw [n_bytes,PV_LIB_SPEC_RebasedCaptures18.n_bytes]
    exact PV_OWN2_ByteImageInverse.decode_pointerBytes one

theorem f_typed : TypedMemory 0 (fun _ => some ()) state ⟨places.f,[()]⟩ := by
  constructor
  · refine ⟨2,PV_LIB_SPEC_RebasedCaptures18.fHeader,receivers.2.2.1,
      Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    change 1 ≤ Aeneas.Std.Usize.max
    scalar_tac
  · intro id h selected
    change receiver state places.f = some (id,h) at selected
    rw [receivers.2.2.1] at selected
    cases selected
    exact ⟨rfl,by intro i bound; rfl⟩

theorem tasks_typed : TypedMemory 0 (fun _ => some ()) state ⟨places.handles,[]⟩ := by
  constructor
  · exact ⟨3,PV_LIB_SPEC_RebasedCaptures18.taskHeader,receivers.2.2.2,
      Or.inr ⟨rfl,rfl⟩,rfl,Nat.zero_le _⟩
  · intro id h selected
    change receiver state places.handles = some (id,h) at selected
    rw [receivers.2.2.2] at selected
    cases selected
    exact ⟨rfl,by intro i bound; simp at bound⟩

theorem fresh : PV_EVHB_SourceLifetimes.Fresh state := by
  intro p id selected
  change PV_LIB_SPEC_RebasedCaptures18.state.places p = some id at selected
  change id < 4
  simp only [PV_LIB_SPEC_RebasedCaptures18.state] at selected
  split at selected
  · cases selected; decide
  · split at selected
    · cases selected; decide
    · split at selected
      · cases selected; decide
      · split at selected
        · cases selected; decide
        · cases selected

theorem owner (counter : Nat) (positive : 0<counter) :
    PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed state counter := by
  refine ⟨fresh,?_⟩
  intro p id selected
  change PV_LIB_SPEC_RebasedCaptures18.state.places p = some id at selected
  simp only [PV_LIB_SPEC_RebasedCaptures18.state] at selected
  split at selected
  · rename_i equal; subst p; exact positive
  · split at selected
    · rename_i equal; subst p; exact positive
    · split at selected
      · rename_i equal; subst p; exact positive
      · split at selected
        · rename_i equal; subst p; exact positive
        · cases selected

theorem captured :
    PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' state captures closure := by
  refine ⟨places,⟨run_typed,n_typed,f_typed,
    tasks_typed,?_,?_,?_⟩,?_⟩
  · intro id h selected
    change receiver state places.run = some (id,h) at selected
    change receiver state places.run = some (id,h) at selected
    rw [receivers.1] at selected
    cases selected; rfl
  · intro id h selected
    change receiver state places.n = some (id,h) at selected
    change receiver state places.n = some (id,h) at selected
    rw [receivers.2.1] at selected
    cases selected; rfl
  · intro id h selected
    change receiver state places.f = some (id,h) at selected
    rw [receivers.2.2.1] at selected
    cases selected; rfl
  · exact ⟨.null,[],⟨0,12,[]⟩,2,rfl,rfl,rfl⟩

theorem validity : RegisteredValidity state := by
  intro p id h selected found
  change PV_LIB_SPEC_RebasedCaptures18.state.places p = some id at selected
  change PV_EVHB_RawVecOwner.lookup PV_LIB_SPEC_RebasedCaptures18.state.world id = some h at found
  simp only [PV_LIB_SPEC_RebasedCaptures18.state] at selected
  split at selected
  · cases selected
    have eq : h = PV_LIB_SPEC_RebasedCaptures18.runHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_RebasedCaptures18.state] using found.symm
    subst h
    exact ⟨by decide,by decide,by decide,by decide⟩
  · split at selected
    · cases selected
      have eq : h = PV_LIB_SPEC_RebasedCaptures18.nHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_RebasedCaptures18.state] using found.symm
      subst h
      exact ⟨by decide,by decide,by decide,by decide⟩
    · split at selected
      · cases selected
        have eq : h = PV_LIB_SPEC_RebasedCaptures18.fHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_RebasedCaptures18.state] using found.symm
        subst h
        exact ⟨by decide,by decide,by decide,by decide⟩
      · split at selected
        · cases selected
          have eq : h = PV_LIB_SPEC_RebasedCaptures18.taskHeader := by simpa [PV_EVHB_RawVecOwner.lookup,PV_LIB_SPEC_RebasedCaptures18.state] using found.symm
          subst h
          exact ⟨by decide,by decide,by decide,by decide⟩
        · cases selected


/-- Future native/resource replies do not enter this entry proof. In
particular the initialized TLS/counter/native Thread coexist with all original
capture and ownership clauses on ONE initial world. Still ENTRY-only. -/
theorem pre : OwnInit.Pre PV_LIB_SPEC_SuccessSchedule12.parameters input := by
  refine ⟨rfl,rfl,owner 2 (by decide),
    owner 1 (by decide),validity,
    ?_,?_,?_⟩
  · constructor
    · intro c eq
      cases eq
      exact ⟨by decide,True.intro,True.intro⟩
    · intro c member; cases member
  · intro v address reached deref
    have valid : PV_LIB_SPEC_ConcreteEntry.Value v := by
      clear deref
      induction reached with
      | argument member =>
        change _ ∈ [.number 1,PV_LIB_SPEC_RebasedCaptures18.closure] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact .count
        · rcases List.mem_singleton.mp member with rfl; exact .closure
      | field n _ selected ih => exact PV_LIB_SPEC_ConcreteEntry.fields _ _ n ih selected
      | pointee _ selected read ih =>
        have eq := PV_LIB_SPEC_ConcreteEntry.dereference _ _ ih selected
        subst eq
        change some Data.null = some _ at read
        cases read
        exact .unit
    have eq := PV_LIB_SPEC_ConcreteEntry.dereference v address valid deref
    subst address
    exact ⟨.null,rfl⟩
  · exact ⟨Unit,Unit,captures,rfl,captured⟩

#print axioms memory_before
#print axioms receivers
#print axioms run_bytes
#print axioms n_bytes
#print axioms run_typed
#print axioms n_typed
#print axioms f_typed
#print axioms tasks_typed
#print axioms fresh
#print axioms validity
#print axioms owner
#print axioms captured
#print axioms pre
end PV_LIB_SPEC_RebasedPre18

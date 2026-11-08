import PV_STX2_ToVecCallSpecification
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Source7Entry
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_Source7EntryOwned

/-- Explicit sixteen-column value, including the empty-slice validity case. -/
def column : alloc.vec.Vec PV_OWN2_Codec.M31 := ⟨[],by simp⟩
def foundation : Foundation := ⟨⟨List.replicate 16 column,by simp⟩⟩
def shape : R1Z.PV_FXM_ReserveWorld.Shape := ⟨4,._Align1Shl2⟩
def header : Header := ⟨4,0,0,shape,true⟩
def source : Place := ⟨0,[4]⟩

/-- A completely concrete OWNER. There are no allocated heap blocks; empty
Rust references are nevertheless non-null and aligned. No resource reply is
fixed here and no successful branch of the clone is assumed. -/
def state : OWNER :=
  {world := {
    allocator := {backend := {},metadata := fun _ => none}
    allocCalls := 0, reallocCalls := 0, deallocCalls := 0
    successfulAlloc := 0, successfulRealloc := 0, drops := 0
    history := [],memory := fun _ => none,live := fun _ => false
    frame := {rest := (),slots := fun id => if id = 0 then some header else none}}
   next := 1
   places := fun p => if p.activation = 0 then some 0 else none}

theorem values_empty (i : Fin foundation.c1.val.length) : values foundation i = [] := by
  change ((List.replicate 16 column)[i.val]).val = []
  rw [List.getElem_replicate]
  rfl

theorem receiver_source : receiver state source = some (0,header) := by
  simp [receiver,PV_EVHB_OwnerMachine.receiver,state,source,lookup]

theorem typed_source : PV_OWN2_Codec.TypedMemory 4 PV_OWN2_Codec.decodeM31 state ⟨source,[]⟩ := by
  constructor
  · exact ⟨0,header,receiver_source,Or.inr ⟨rfl,rfl⟩,rfl,by decide⟩
  · intro id h selected
    rw [receiver_source] at selected
    cases selected
    exact ⟨rfl,by intro i bound; simp at bound⟩

theorem owned : Source7EntryOwned state foundation := by
  intro i
  refine ⟨source,0,header,rfl,rfl,?_,rfl,?_⟩
  · rw [values_empty]; exact Nat.zero_le _
  · rw [values_empty]; exact typed_source

theorem chosen_header (i : Fin foundation.c1.val.length) :
    PV_STX2_Source7EntrySelection.header owned i = header := by
  have h := (PV_STX2_Source7EntrySelection.selected owned i).2.1
  change (if PV_STX2_Source7EntrySelection.identity owned i = 0 then some header else none) =
    some (PV_STX2_Source7EntrySelection.header owned i) at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem identity_zero (i : Fin foundation.c1.val.length) :
    PV_STX2_Source7EntrySelection.identity owned i = 0 := by
  have h := (PV_STX2_Source7EntrySelection.selected owned i).1
  change (if (PV_STX2_Source7EntrySelection.place owned i).activation = 0 then some 0 else none) =
    some (PV_STX2_Source7EntrySelection.identity owned i) at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem identities : PV_STX2_OwnerWellFormed.OwnerWellFormed state := by
  intro p id selected
  change (if p.activation = 0 then some 0 else none) = some id at selected
  split at selected
  · cases selected; exact Nat.zero_lt_succ 0
  · cases selected

theorem indexed : PV_STX2_Source7EntryOwnedIndexed.Source7EntryOwned''' state foundation :=
  ⟨owned,identities,by
    intro i
    rw [(PV_STX2_Source7EntrySelection.selected owned i).1,identity_zero]
    rfl⟩

theorem aligned : PV_STX2_Source7EntryOwnedAligned.Source7EntryOwned'''' state foundation :=
  ⟨indexed,by
    intro i
    change (PV_STX2_Source7EntrySelection.header owned i).pointer % 4 = 0
    rw [chosen_header]
    rfl⟩

theorem valid : PV_STX2_Source7EntryReferenceValid.Source7EntryOwned''''' state foundation :=
  ⟨aligned,by
    intro i
    change (PV_STX2_Source7EntrySelection.header owned i).pointer ≠ 0
    rw [chosen_header]
    decide,
   by
    intro i
    change (PV_STX2_Source7EntrySelection.header owned i).pointer + (values foundation i).length*4 ≤ 2^64
    rw [chosen_header,values_empty]
    decide⟩

theorem owner_wellFormed : PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed state 1 := by
  refine ⟨⟨⟨identities,?_⟩,?_⟩,?_⟩
  · intro p id selected
    change (if p.activation = 0 then some 0 else none) = some id at selected
    split at selected
    · next h => rw [h]; exact Nat.zero_lt_succ 0
    · cases selected
  · intro pointer allocation selected
    cases selected
  · intro pointer allocation selected
    cases selected

/-- JOINT witness for the entry/reference/OWNER component only. The complete
source7 machine/environment/representation conjunction is not asserted. -/
theorem entry_nonempty :
    ∃ (w : OWNER) (v : Foundation),
      PV_STX2_Source7EntryReferenceValid.Source7EntryOwned''''' w v ∧
      PV_STX2_OwnerAllocationReferenceValid.OwnerWellFormed w 1 :=
  ⟨state,foundation,valid,owner_wellFormed⟩

open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

def store : Store Data := {cells := fun _ => none,nextActivation := 1}
def toVecEntry : PV_STX2_ToVecCallSummary.Entry :=
  {store := store,parents := [],caller := 0,pointer := ⟨0,4,[]⟩,length := 0,
   owner := state,prior := [],region := ⟨source,[]⟩,sourceId := 0,sourceHeader := header}

theorem toVec_pre : PV_STX2_ToVecCallSummary.Pre toVecEntry := by
  have argument : PV_STX2_ToVecCallArgumentEntry.Pre state ⟨source,[]⟩ 0 header :=
    ⟨rfl,rfl,by decide,rfl,typed_source,rfl,identities⟩
  refine ⟨?_,?_,?_⟩
  · exact ⟨⟨⟨argument,owner_wellFormed.previous.previous⟩,rfl,rfl⟩,
      owner_wellFormed,by decide,rfl,by decide⟩
  · apply PV_STX2_ToVecCallNumberedEntry.start
    exact ⟨by decide,trivial,trivial⟩
  · change 0 < 2^64
    decide

theorem toVec_entry_nonempty : ∃ e : PV_STX2_ToVecCallSummary.Entry,
    PV_STX2_ToVecCallSummary.Pre e := ⟨toVecEntry,toVec_pre⟩

#print axioms values_empty
#print axioms receiver_source
#print axioms typed_source
#print axioms owned
#print axioms chosen_header
#print axioms identity_zero
#print axioms identities
#print axioms indexed
#print axioms aligned
#print axioms valid
#print axioms owner_wellFormed
#print axioms entry_nonempty
#print axioms toVec_pre
#print axioms toVec_entry_nonempty
end PV_LIB_SPEC_Source7Entry

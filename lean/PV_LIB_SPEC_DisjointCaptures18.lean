import PV_LIB_SPEC_F361Contract
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_DisjointCaptures18
open Aeneas Aeneas.Std PV_EVHB_OWNER PV_EVHB_RawVecOwner PV_OWN2_Codec
open PV_OWN2_RunBorrowAddress PV_EVHB_OrderedFamiliesEntry

def site : Site := ⟨1019408,1027216,918608,112,64,.localSlot 104⟩
def zero : Pointer := ⟨1024,by decide⟩
def one : Pointer := ⟨1,by decide⟩
def captures : Captures Unit Unit :=
  ⟨site,zero,zero,one,(),[],0,fun _ => some (),0,fun _ => some ()⟩
def places : Places := ⟨⟨0,[10]⟩,⟨0,[11]⟩,⟨0,[12]⟩,⟨0,[13]⟩⟩
def runHeader : Header := ⟨1136,1,1,⟨16,._Align1Shl3⟩,false⟩
def nHeader : Header := ⟨1088,1,1,⟨8,._Align1Shl3⟩,false⟩
def fHeader : Header := ⟨1128,1,1,⟨0,._Align1Shl0⟩,false⟩
def taskHeader : Header := ⟨8,0,0,⟨0,._Align1Shl0⟩,true⟩
def bytes (p : Nat) : Option Nat :=
  if h : 1136 ≤ p ∧ p < 1152 then
    some (PV_OWN2_OperandImages.pairBytes (runWords site zero zero).1
      (runWords site zero zero).2 ⟨p-1136,by omega⟩).val
  else if h : 1088 ≤ p ∧ p < 1096 then
    some (PV_OWN2_WordImage.pointerBytes one ⟨p-1088,by omega⟩).val else none

def state : OWNER :=
  {world := {
    allocator := {backend := {},metadata := fun p =>
      if p = 1136 then some (layout runHeader 1)
      else if p = 1088 then some (layout nHeader 1)
      else if p = 1128 then some (layout fHeader 1) else none}
    allocCalls := 0,reallocCalls := 0,deallocCalls := 0
    successfulAlloc := 0,successfulRealloc := 0,drops := 0
    history := [],memory := bytes,live := fun p => p = 1136 || p = 1088 || p = 1128
    frame := {rest := (),slots := fun id =>
      if id = 0 then some runHeader else if id = 1 then some nHeader
      else if id = 2 then some fHeader else if id = 3 then some taskHeader else none}}
   next := 4
   places := fun p => if p = places.run then some 0 else if p = places.n then some 1
      else if p = places.f then some 2 else if p = places.handles then some 3 else none}

theorem receivers :
    receiver state places.run = some (0,runHeader) ∧
    receiver state places.n = some (1,nHeader) ∧
    receiver state places.f = some (2,fHeader) ∧
    receiver state places.handles = some (3,taskHeader) := by
  simp [receiver,PV_EVHB_OwnerMachine.receiver,state,places,lookup]

theorem run_bytes :
    PV_STX_OriginalCopyTyped.bytesAt state.world.memory 1136 16 0 =
      fun i => some (PV_OWN2_OperandImages.pairBytes
        (runWords site zero zero).1 (runWords site zero zero).2 i).val := by
  funext i
  simp only [PV_STX_OriginalCopyTyped.bytesAt,state,Nat.zero_mul,Nat.add_zero]
  have range : 1136 ≤ 1136+i.val ∧ 1136+i.val < 1152 := by omega
  simp only [bytes,dif_pos range,Nat.add_sub_cancel_left]

theorem n_bytes :
    PV_STX_OriginalCopyTyped.bytesAt state.world.memory 1088 8 0 =
      fun i => some (PV_OWN2_WordImage.pointerBytes one i).val := by
  funext i
  simp only [PV_STX_OriginalCopyTyped.bytesAt,state,Nat.zero_mul,Nat.add_zero]
  have outside : ¬ (1136 ≤ 1088+i.val ∧ 1088+i.val < 1152) := by omega
  have inside : 1088 ≤ 1088+i.val ∧ 1088+i.val < 1096 := by omega
  simp only [bytes,dif_neg outside,dif_pos inside,Nat.add_sub_cancel_left]

theorem run_typed : TypedMemory 16 decodeFatPointer state
    ⟨places.run,[runWords site zero zero]⟩ := by
  constructor
  · refine ⟨0,runHeader,receivers.1,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    decide
  · intro id h selected
    rw [receivers.1] at selected
    cases selected
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i = 0 := by simpa using bound
    subst i
    change decodeFatPointer (PV_STX_OriginalCopyTyped.bytesAt state.world.memory 1136 16 0) = some (runWords site zero zero)
    rw [run_bytes]
    exact PV_OWN2_OperandImages.decode_pairBytes _ _

theorem n_typed : UsizeMemory state ⟨places.n,[one]⟩ := by
  constructor
  · refine ⟨1,nHeader,receivers.2.1,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    decide
  · intro id h selected
    rw [receivers.2.1] at selected
    cases selected
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i = 0 := by simpa using bound
    subst i
    change decodePointer (PV_STX_OriginalCopyTyped.bytesAt state.world.memory 1088 8 0) = some one
    rw [n_bytes]
    exact PV_OWN2_ByteImageInverse.decode_pointerBytes one

theorem f_typed : TypedMemory 0 (fun _ => some ()) state ⟨places.f,[()]⟩ := by
  constructor
  · refine ⟨2,fHeader,receivers.2.2.1,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
    change 1 ≤ Usize.max
    scalar_tac
  · intro id h selected
    rw [receivers.2.2.1] at selected
    cases selected
    refine ⟨rfl,?_⟩
    intro i bound
    have eq : i = 0 := by simpa using bound
    subst i
    rfl

theorem tasks_typed : TypedMemory 0 (fun _ => some ()) state ⟨places.handles,[]⟩ := by
  constructor
  · exact ⟨3,taskHeader,receivers.2.2.2,Or.inr ⟨rfl,rfl⟩,rfl,Nat.zero_le _⟩
  · intro id h selected
    rw [receivers.2.2.2] at selected
    cases selected
    exact ⟨rfl,by intro i bound; simp at bound⟩

def closure : PV_STX2_Syntax.Data := PV_THR2_KeyValues.pack .null
  [PV_STX2_TypedReferences.reference ⟨0,12,[]⟩ .null]

/-- SPEC-C13 repair: parent stack4096, run4208, n4160 and F4200.
The adopted site offsets are unchanged. One initialized original-capture domain. This is an ENTRY
component witness only: it does not supply all machine/resource/child premises
or prove an OwnInit row, a reached Some branch or a binary association. -/
theorem entry_nonempty :
    PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' state captures closure := by
  refine ⟨places,⟨run_typed,n_typed,f_typed,tasks_typed,?_,?_,?_⟩,?_⟩
  · intro id h selected
    change receiver state places.run = some (id,h) at selected
    rw [receivers.1] at selected
    cases selected
    rfl
  · intro id h selected
    change receiver state places.n = some (id,h) at selected
    rw [receivers.2.1] at selected
    cases selected
    rfl
  · intro id h selected
    change receiver state places.f = some (id,h) at selected
    rw [receivers.2.2.1] at selected
    cases selected
    rfl
  · exact ⟨.null,[],⟨0,12,[]⟩,2,rfl,rfl,rfl⟩

#print axioms site
#print axioms zero
#print axioms one
#print axioms captures
#print axioms places
#print axioms runHeader
#print axioms nHeader
#print axioms fHeader
#print axioms taskHeader
#print axioms bytes
#print axioms state
#print axioms receivers
#print axioms run_bytes
#print axioms n_bytes
#print axioms run_typed
#print axioms n_typed
#print axioms f_typed
#print axioms tasks_typed
#print axioms closure
#print axioms entry_nonempty
end PV_LIB_SPEC_DisjointCaptures18

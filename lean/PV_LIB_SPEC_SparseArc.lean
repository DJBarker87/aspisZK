import PV_LIB_SPEC_ArcImageGap
import PV_THR2_PacketBoxImageOwned
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SparseArc
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
/-- Adopted client ELF fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558.
Malloc at e058a: 48/8. Stores e059c/e05a3/e05ab/e05b3 write offsets
0/8/16/24 only. SESSION7_ABI_BINARY.txt retains the instructions. -/
def shape : R1Z.PV_FXM_ReserveWorld.Shape := ⟨48,._Align1Shl3⟩
abbrev image := PV_LIB_SPEC_ArcImageGap.initialImage
/-- Sparse overwrite: absence in the image RETAINS pre-memory, including a
concrete stale byte. No observer projection or zero initialization is used. -/
def memory (p scope : Nat) (before : Nat → Option Nat) (address : Nat) : Option Nat :=
  if p ≤ address then
    match image scope (address-p) with
    | some b => some b.val
    | none => before address
  else before address

def initialized (p scope : Nat) (w : OWNER) : OWNER :=
  {w with world := {w.world with memory := memory p scope w.world.memory}}

theorem binary_agreement (p scope : Nat) (w : OWNER) :
    initialized p scope w = PV_LIB_SPEC_ArcImageGap.binaryInitialized p scope w := by
  have mem : memory p scope w.world.memory =
      PV_LIB_SPEC_ArcImageGap.initializedMemory p scope w.world.memory := by
    funext address
    unfold memory PV_LIB_SPEC_ArcImageGap.initializedMemory
    by_cases lower : p ≤ address
    · by_cases upper : address < p+32
      · rw [if_pos lower,if_pos ⟨lower,upper⟩]
        have small : address-p < 32 := by omega
        have present : ∃ b, image scope (address-p) = some b := by
          unfold image PV_LIB_SPEC_ArcImageGap.initialImage
          split
          · exact ⟨_,rfl⟩
          · split
            · exact ⟨_,rfl⟩
            · split
              · exact ⟨_,rfl⟩
              · exact ⟨_,rfl⟩
        obtain ⟨b,stored⟩ := present
        change _ = Option.map Fin.val (image scope (address-p))
        rw [stored]; rfl
      · rw [if_pos lower,if_neg (by omega)]
        have hole : image scope (address-p) = none :=
          PV_LIB_SPEC_ArcImageGap.source_hole scope (address-p) (by omega)
        rw [hole]
    · rw [if_neg lower,if_neg (by omega)]
  simp only [initialized,PV_LIB_SPEC_ArcImageGap.binaryInitialized,mem]

theorem written (p scope i : Nat) (w : OWNER) (b : Fin 256)
    (stored : image scope i = some b) :
    (initialized p scope w).world.memory (p+i) = some b.val := by
  change memory p scope w.world.memory (p+i) = _
  simp only [memory,if_pos (by omega : p ≤ p+i),Nat.add_sub_cancel_left,stored]

theorem unwritten (p scope address : Nat) (w : OWNER)
    (hole : image scope (address-p) = none) :
    (initialized p scope w).world.memory address = w.world.memory address := by
  change memory p scope w.world.memory address = _
  unfold memory
  split <;> simp only [hole]

theorem payload (p scope i : Nat) (w : OWNER) (hole : 32 ≤ i) :
    (initialized p scope w).world.memory (p+i) = w.world.memory (p+i) := by
  apply unwritten
  rw [Nat.add_sub_cancel_left]
  exact PV_LIB_SPEC_ArcImageGap.source_hole scope i hole

theorem descriptor (p scope : Nat) (w : OWNER) (place : PV_EVHB_OwnerMachine.Place) :
    receiver (initialized p scope w) place = receiver w place := rfl

theorem owned (p scope : Nat) (w : OWNER) (id : Nat) :
    OwnedAt (initialized p scope w).world id ↔ OwnedAt w.world id := Iff.rfl

/-- Same named allocation, registration, header, event and all-answer models
as the provider. ONLY the successful initialization suffix becomes sparse.
The scope word is source data, not a total image or a desired byte function.
Association with the source Packet operand is a separate partial codec. -/
def reply (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scope : Nat) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  let r := PV_THR2_PacketBoxResource.reply resources encode s w shape 8
  let out := PV_THR2_PacketBoxReply.finish s w.next
    (PV_EVHB_SourceLifetimes.emptyHeader shape 8) r
  match r.answer with
  | .returned (.ok p) => if p=0 then out else
      {out with world := initialized p scope out.world}
  | _ => out

theorem returned (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scope p : Nat)
    (answer : (resources (.malloc 48) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) :
    let r := PV_THR2_PacketBoxResource.reply resources encode s w shape 8
    let out := PV_THR2_PacketBoxReply.finish s w.next
      (PV_EVHB_SourceLifetimes.emptyHeader shape 8) r
    reply resources encode s w scope =
      ⟨.returned (.ok (PV_THR2_PacketBoxReply.value s)),
        initialized p scope out.world,out.events⟩ := by
  intro r out
  have ok : r.answer = .returned (.ok p) :=
    (PV_THR2_PacketBoxResource.answer resources encode s w shape 8).trans answer
  have done := PV_THR2_PacketBoxReply.returned s w.next p
    (PV_EVHB_SourceLifetimes.emptyHeader shape 8) r ok nonnull
  change (match r.answer with
    | .returned (.ok q) => if q=0 then out else {out with world := initialized q scope out.world}
    | _ => out) = _
  simp only [ok,if_neg nonnull]
  have value : out.answer = .returned (.ok (PV_THR2_PacketBoxReply.value s)) := by
    dsimp only [out]; rw [done]
  rw [value]

/-- Rechecked ownership/pointer result: the last conjunct of the old total
image theorem is replaced by the SPARSE stored-byte law AND the hole frame. -/
theorem returned_owned (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scope p : Nat)
    (answer : (resources (.malloc 48) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) :
    let out := reply resources encode s w scope
    out.answer = .returned (.ok (PV_THR2_PacketBoxReply.value s)) ∧
    OwnedAt out.world.world w.next ∧
    receiver out.world (PV_THR2_PacketBoxRegister.place s) = some (w.next,
      capacityStore (pointerStore (PV_EVHB_SourceLifetimes.emptyHeader shape 8) p) 1) ∧
    (∀ i b, image scope i = some b → out.world.world.memory (p+i) = some b.val) ∧
    (∀ i, 32 ≤ i → out.world.world.memory (p+i) =
      (PV_THR2_PacketBoxReply.finish s w.next
        (PV_EVHB_SourceLifetimes.emptyHeader shape 8)
        (PV_THR2_PacketBoxResource.reply resources encode s w shape 8)).world.world.memory (p+i)) := by
  intro out
  have resource := PV_THR2_PacketBoxResourceOwned.returned resources encode s w shape 8 p answer nonnull
  have pointer := PV_THR2_PacketBoxPointerAssociation.returned resources encode s w shape 8 p answer nonnull
  dsimp only [out]
  rw [returned resources encode s w scope p answer nonnull]
  exact ⟨rfl,resource.2,pointer,fun i b h => written p scope i _ b h,fun i h => payload p scope i _ h⟩

/-- Every unsuccessful/null resource branch is EXACTLY the previous finish.
No decode or sparse-image application takes place on those branches. -/
theorem other (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (scope : Nat)
    (unsuccessful : ∀ p, (resources (.malloc 48) (world w)).answer = .returned (.ok p) → p=0) :
    reply resources encode s w scope =
      PV_THR2_PacketBoxReply.finish s w.next
        (PV_EVHB_SourceLifetimes.emptyHeader shape 8)
        (PV_THR2_PacketBoxResource.reply resources encode s w shape 8) := by
  have h := PV_THR2_PacketBoxResource.answer resources encode s w shape 8
  unfold reply
  dsimp only
  cases eq : (PV_THR2_PacketBoxResource.reply resources encode s w shape 8).answer with
  | returned result =>
    cases result with
    | ok p => simp only [if_pos (unsuccessful p (h.symm.trans eq))]
    | fail e => rfl
    | div => rfl
  | fault f => rfl
  | pending => rfl

#print axioms shape
#print axioms image
#print axioms memory
#print axioms initialized
#print axioms binary_agreement
#print axioms written
#print axioms unwritten
#print axioms payload
#print axioms descriptor
#print axioms owned
#print axioms reply
#print axioms returned
#print axioms returned_owned
#print axioms other
end PV_LIB_SPEC_SparseArc

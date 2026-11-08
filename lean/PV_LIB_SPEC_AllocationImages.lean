import PV_LIB_SPEC_SparseArc
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_AllocationImages
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
/-- Outer none means NO STORE; some none is a real copy of an unknown source
byte. Keeping these separate prevents a memcpy from inventing padding bytes. -/
abbrev Image := Nat → Option (Option Nat)
abbrev Memory := Nat → Option Nat
abbrev byte := PV_LIB_SPEC_ArcImageGap.byte

def word (value i : Nat) : Option (Option Nat) := some (some (byte value i).val)

/-- fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558,
fa099 malloc40/8; fa0b3/fa0ba/fa0c2/fa0c6 qwords0/8/16/24;
fa0ce byte32. Thread is the actual current_or_unnamed return in r14.
Source declaration order is counter,panic,thread; native order is thread,counter,panic. -/
def scope (thread : Nat) : Image := fun i =>
  if i < 8 then word 1 i else if i < 16 then word 1 (i-8)
  else if i < 24 then word thread (i-16) else if i < 32 then word 0 (i-24)
  else if i=32 then some (some 0) else none

/-- Same ELF, e058a malloc48/8; four stores e059c/e05a3/e05ab/e05b3.
Packet has a different layout and absent-result niche from ScopeData. -/
def packet (scopePointer : Nat) : Image := fun i =>
  (PV_LIB_SPEC_SparseArc.image scopePointer i).map (fun b => some b.val)

/-- Same ELF, e05e8 malloc56/8. e0619 copies rsp+0x38..0x47 to0..15;
e0614 copies rsp+0x48..0x57 to16..31; e061d/e0621/e0625 store r12/rcx/rax
at32/40/48. Source bytes include padding and are SNAPSHOTTED before stores. -/
def callback (before : Memory) (rsp packetPointer capturePointer captureLength : Nat) : Image := fun i =>
  if i < 32 then some (before (rsp+0x38+i))
  else if i < 40 then word packetPointer (i-32)
  else if i < 48 then word capturePointer (i-40)
  else if i < 56 then word captureLength (i-48) else none

/-- Same ELF, e064b malloc24/8; e065a/e065d/e0668 qwords0/8/16.
All24 bytes are written. Values are actual handle, callback allocation and
relocated vtable operands, not a total-image parameter. -/
def threadInit (handle callbackPointer vtable : Nat) : Image := fun i =>
  if i < 8 then word handle i else if i < 16 then word callbackPointer (i-8)
  else if i < 24 then word vtable (i-16) else none

/-- Same ELF, Thread::new at17be40 (GOT1b3758 from call e0541),
ArcInner < thread::Inner>:48/8. 17bedc/17bee3/17bef3/17beeb/17beef
qwords0/8/16/24/32;17bef7 dword40. Tail44..47 is not stored.
The absent-name case STILL stores r14 at32; it is not replaced by zero. -/
def threadInner (id namePointer nameLength : Nat) : Image := fun i =>
  if i < 8 then word 1 i else if i < 16 then word 1 (i-8)
  else if i < 24 then word id (i-16) else if i < 32 then word namePointer (i-24)
  else if i < 40 then word nameLength (i-32)
  else if i < 44 then some (some 0) else none

def overwrite (p : Nat) (image : Image) (before : Memory) : Memory := fun address =>
  if p ≤ address then (image (address-p)).getD (before address) else before address

def initialized (p : Nat) (image : Image) (w : OWNER) : OWNER :=
  {w with world := {w.world with memory := overwrite p image w.world.memory}}

theorem stored (p i : Nat) (image : Image) (before : Memory) (value : Option Nat)
    (store : image i = some value) : overwrite p image before (p+i) = value := by
  simp only [overwrite,if_pos (by omega : p ≤ p+i),Nat.add_sub_cancel_left,store,Option.getD_some]

theorem hole (p address : Nat) (image : Image) (before : Memory)
    (absent : image (address-p) = none) : overwrite p image before address = before address := by
  unfold overwrite
  split <;> simp only [absent,Option.getD_none]

theorem scope_hole (thread i : Nat) (tail : 33 ≤ i) : scope thread i = none := by
  simp only [scope,if_neg (by omega : ¬ i < 8),if_neg (by omega : ¬ i < 16),
    if_neg (by omega : ¬ i < 24),if_neg (by omega : ¬ i < 32),if_neg (by omega : i ≠ 32)]

theorem packet_hole (scopePointer i : Nat) (tail : 32 ≤ i) : packet scopePointer i = none := by
  simp only [packet,PV_LIB_SPEC_SparseArc.image,PV_LIB_SPEC_ArcImageGap.source_hole scopePointer i tail,Option.map_none]

theorem callback_copy (p rsp packetPointer capturePointer captureLength i : Nat)
    (before : Memory) (copied : i < 32) :
    overwrite p (callback before rsp packetPointer capturePointer captureLength) before (p+i) =
      before (rsp+0x38+i) := by
  apply stored
  exact if_pos copied

theorem callback_hole (before : Memory) (rsp packetPointer capturePointer captureLength i : Nat)
    (tail : 56 ≤ i) : callback before rsp packetPointer capturePointer captureLength i = none := by
  simp only [callback,if_neg (by omega : ¬ i < 32),if_neg (by omega : ¬ i < 40),
    if_neg (by omega : ¬ i < 48),if_neg (by omega : ¬ i < 56)]

theorem init_hole (handle callbackPointer vtable i : Nat) (tail : 24 ≤ i) :
    threadInit handle callbackPointer vtable i = none := by
  simp only [threadInit,if_neg (by omega : ¬ i < 8),if_neg (by omega : ¬ i < 16),if_neg (by omega : ¬ i < 24)]

theorem thread_hole (id namePointer nameLength i : Nat) (tail : 44 ≤ i) :
    threadInner id namePointer nameLength i = none := by
  simp only [threadInner,if_neg (by omega : ¬ i < 8),if_neg (by omega : ¬ i < 16),
    if_neg (by omega : ¬ i < 24),if_neg (by omega : ¬ i < 32),if_neg (by omega : ¬ i < 40),if_neg (by omega : ¬ i < 44)]

theorem packet_agreement (p scopePointer : Nat) (w : OWNER) :
    initialized p (packet scopePointer) w = PV_LIB_SPEC_SparseArc.initialized p scopePointer w := by
  have mem : overwrite p (packet scopePointer) w.world.memory =
      PV_LIB_SPEC_SparseArc.memory p scopePointer w.world.memory := by
    funext address
    unfold overwrite PV_LIB_SPEC_SparseArc.memory
    split
    · dsimp only [packet]
      cases PV_LIB_SPEC_SparseArc.image scopePointer (address-p) <;> rfl
    · rfl
  simp only [initialized,PV_LIB_SPEC_SparseArc.initialized,mem]

theorem ghost (p : Nat) (image : Image) (w : OWNER) :
    (initialized p image w).next = w.next ∧ (initialized p image w).places = w.places ∧
    (initialized p image w).world.frame = w.world.frame := ⟨rfl,rfl,rfl⟩

theorem receiver_frame (p : Nat) (image : Image) (w : OWNER) (place : Place) :
    receiver (initialized p image w) place = receiver w place := rfl

theorem owned_frame (p : Nat) (image : Image) (w : OWNER) (id : Nat) :
    OwnedAt (initialized p image w).world id ↔ OwnedAt w.world id := Iff.rfl

#print axioms word
#print axioms scope
#print axioms packet
#print axioms callback
#print axioms threadInit
#print axioms threadInner
#print axioms overwrite
#print axioms initialized
#print axioms stored
#print axioms hole
#print axioms scope_hole
#print axioms packet_hole
#print axioms callback_copy
#print axioms callback_hole
#print axioms init_hole
#print axioms thread_hole
#print axioms packet_agreement
#print axioms ghost
#print axioms receiver_frame
#print axioms owned_frame
end PV_LIB_SPEC_AllocationImages

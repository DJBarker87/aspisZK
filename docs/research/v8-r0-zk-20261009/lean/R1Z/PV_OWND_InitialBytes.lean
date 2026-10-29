import R1Z.PV_OWND_AllocationBuffer
import R1Z.PV_OWND_PushSuffix
import R1Z.PV_OWND_LegacyCount
set_option autoImplicit false
attribute [local irreducible] R1Z.PV_OWNC_PushFold.append R1Z.PV_OWND_LegacySource.links
namespace R1Z.PV_OWND_InitialBytes
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading
/-- Actual allocation post-world followed by the 127 source-ordered stores. -/
def initialized (m : Memory) (t : Token) (owner : Nat) : Buffer Link :=
 PV_OWNC_PushFold.append PV_OWNB_LinkCodec.codec
  (PV_OWND_AllocationBuffer.buffer PV_OWNB_LinkCodec.codec 127 owner m t ⟨.ownerOutput,0,0⟩)
  PV_OWND_LegacySource.links

theorem valid {S X E : Type} (prim : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (owner p : Nat) (s : S)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (loans:NoLoans w.memory ⟨p,w.memory.generations p+1⟩) :
 PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec
  (initialized (allocate prim ⟨1016,2⟩ owner w).world.memory
   ⟨p,w.memory.generations p+1⟩ owner) := by
 unfold initialized
 apply PV_OWNC_PushFold.valid
 · exact PV_OWND_AllocationBuffer.valid _ 127 owner _ prim w p s h loans
 · change 0+PV_OWND_LegacySource.links.length≤127
   rw [PV_OWND_LegacyCount.count]
   omega
 · exact PV_OWNB_LinkBound.bounded

theorem length (m : Memory) (t : Token) (owner : Nat) :
 (initialized m t owner).length=127 := by
 rw [initialized,PV_OWNC_PushFold.length,PV_OWND_LegacyCount.count]
 rfl

theorem capacity (m : Memory) (t : Token) (owner : Nat) :
 (initialized m t owner).capacity=127 := by
 rw [initialized,PV_OWNC_PushFold.capacity]
 rfl

theorem values (m : Memory) (t : Token) (owner i : Nat)
 (hi:i<PV_OWND_LegacySource.links.length) :
 (initialized m t owner).values i=PV_OWND_LegacySource.links[i] := by
 unfold initialized
 have h:=PV_OWND_PushSuffix.suffix PV_OWNB_LinkCodec.codec
  (PV_OWND_AllocationBuffer.buffer PV_OWNB_LinkCodec.codec 127 owner m t ⟨.ownerOutput,0,0⟩) PV_OWND_LegacySource.links i hi
 simpa only [PV_OWND_AllocationBuffer.buffer,Nat.zero_add] using h
attribute [local irreducible] initialized
#print axioms valid
#print axioms length
#print axioms capacity
#print axioms values
end R1Z.PV_OWND_InitialBytes

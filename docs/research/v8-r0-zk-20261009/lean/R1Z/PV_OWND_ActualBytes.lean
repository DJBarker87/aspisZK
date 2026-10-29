import R1Z.PV_OWND_PaddedValid
import R1Z.PV_OWND_PaddedHeader
import R1Z.PV_OWND_PaddedValues
import R1Z.PV_OWND_AllocationBuffer
import R1Z.PV_OWND_LegacyCount
set_option autoImplicit false
namespace R1Z.PV_OWND_ActualBytes
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes

def initialized (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) : Buffer Link :=
 PV_OWND_PaddedFold.append PV_OWNB_LinkCodec.codec
  (PV_OWND_AllocationBuffer.buffer PV_OWNB_LinkCodec.codec 127 owner m t ⟨.ownerOutput,0,0⟩)
  PV_OWND_LegacySource.links payload 0

theorem valid {S X E : Type} (prim : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (owner p : Nat) (s : S) (payload : Nat → Link → Bytes)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (loans:NoLoans w.memory ⟨p,w.memory.generations p+1⟩)
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) (payload i v)) :
 PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec
  (initialized (allocate prim ⟨1016,2⟩ owner w).world.memory
   ⟨p,w.memory.generations p+1⟩ owner payload) := by
 unfold initialized
 apply PV_OWND_PaddedValid.valid
 · exact PV_OWND_AllocationBuffer.valid _ 127 owner _ prim w p s h loans
 · change 0+PV_OWND_LegacySource.links.length≤127
   rw [PV_OWND_LegacyCount.count]
   omega
 · exact PV_OWNB_LinkBound.bounded
 · exact agrees
attribute [local irreducible] initialized
#print axioms valid
end R1Z.PV_OWND_ActualBytes

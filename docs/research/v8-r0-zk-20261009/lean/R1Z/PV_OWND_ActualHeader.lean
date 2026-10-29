import R1Z.PV_OWND_ActualBytes
set_option autoImplicit false
attribute [local irreducible] R1Z.PV_OWND_PaddedFold.append R1Z.PV_OWND_LegacySource.links R1Z.PV_OWNB_LinkCodec.codec
namespace R1Z.PV_OWND_ActualHeader
open PV_OWN_Heap PV_OWN_Link PV_OWN_Bytes PV_OWND_ActualBytes

theorem length (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) :
 (initialized m t owner payload).length=127 := by
 rw [initialized,PV_OWND_PaddedHeader.length,PV_OWND_LegacyCount.count]
 rfl

theorem identity (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) :
 let b:=initialized m t owner payload
 b.capacity=127 ∧ b.owner=owner ∧ b.token=t ∧
 b.memory.generations=m.generations ∧ b.memory.slots=m.slots ∧ b.memory.loans=m.loans := by
 exact PV_OWND_PaddedHeader.identity _ _ _ _ _

theorem values (m : Memory) (t : Token) (owner i : Nat) (payload : Nat → Link → Bytes)
 (hi:i<PV_OWND_LegacySource.links.length) :
 (initialized m t owner payload).values i=PV_OWND_LegacySource.links[i] := by
 unfold initialized
 have h:=PV_OWND_PaddedValues.suffix PV_OWNB_LinkCodec.codec
  (PV_OWND_AllocationBuffer.buffer PV_OWNB_LinkCodec.codec 127 owner m t ⟨.ownerOutput,0,0⟩) PV_OWND_LegacySource.links payload 0 i hi
 simpa only [PV_OWND_AllocationBuffer.buffer,Nat.zero_add] using h
#print axioms length
#print axioms identity
#print axioms values
end R1Z.PV_OWND_ActualHeader

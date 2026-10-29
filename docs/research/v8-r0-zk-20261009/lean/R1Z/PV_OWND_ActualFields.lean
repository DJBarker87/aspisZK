import R1Z.PV_OWND_ActualHeader
set_option autoImplicit false
namespace R1Z.PV_OWND_ActualFields
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Every initialized source field is read from the actual authoritative cell.
No endpoint-only logical map replaces the full Link representation. -/
theorem represented {S X E : Type} (prim : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (owner p : Nat) (s : S) (payload : Nat → Link → Bytes)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (loans:NoLoans w.memory ⟨p,w.memory.generations p+1⟩)
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) (payload i v))
 (i : Nat) (hi:i<PV_OWND_LegacySource.links.length) :
 let b:=PV_OWND_ActualBytes.initialized (allocate prim ⟨1016,2⟩ owner w).world.memory
  ⟨p,w.memory.generations p+1⟩ owner payload
 PV_OWNB_LinkCodec.NativeView b.cell (i*8) PV_OWND_LegacySource.links[i] := by
 dsimp only
 have hb:=PV_OWND_ActualBytes.valid prim w owner p s payload h loans agrees
 unfold PV_OWNC_Vector.Valid at hb
 have il:i<(PV_OWND_ActualBytes.initialized (allocate prim ⟨1016,2⟩ owner w).world.memory
   ⟨p,w.memory.generations p+1⟩ owner payload).length := by
  rw [PV_OWND_ActualHeader.length]
  rwa [PV_OWND_LegacyCount.count] at hi
 have view:=hb.2.2.2.2 i il
 rw [PV_OWND_ActualHeader.values _ _ _ i payload hi] at view
 exact view
#print axioms represented
end R1Z.PV_OWND_ActualFields

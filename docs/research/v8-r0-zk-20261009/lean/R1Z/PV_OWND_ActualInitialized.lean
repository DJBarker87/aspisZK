import R1Z.PV_OWND_InitialContext
import R1Z.PV_OWND_ActualFields
set_option autoImplicit false
namespace R1Z.PV_OWND_ActualInitialized
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Allocation and all source-ordered writes construct the full byte/owner
instance. Its permission is derived from incoming live-loan invariants. This
stops before the two stack-array endpoint checks and their caller cleanup. -/
theorem constructed {S X E : Type} (prim : Request → S → Outcome E (Option Nat) × S)
 (w : State S X) (owner p : Nat) (s : S) (payload : Nat → Link → Bytes)
 (ctx:PV_OWND_InitialContext.Context prim w owner)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) (payload i v)) :
 let b:=PV_OWND_ActualBytes.initialized (allocate prim ⟨1016,2⟩ owner w).world.memory
   ⟨p,w.memory.generations p+1⟩ owner payload
 PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec b ∧ b.length=127 ∧ b.capacity=127 ∧
 (∀ i (hi:i<PV_OWND_LegacySource.links.length),
  PV_OWNB_LinkCodec.NativeView b.cell (i*8) PV_OWND_LegacySource.links[i]) := by
 dsimp only
 have loans:=PV_OWND_InitialContext.noLoans prim w owner p s ctx h
 exact ⟨PV_OWND_ActualBytes.valid prim w owner p s payload h loans agrees,
  PV_OWND_ActualHeader.length _ _ _ _,(PV_OWND_ActualHeader.identity _ _ _ _).1,
  fun i hi=>PV_OWND_ActualFields.represented prim w owner p s payload h loans agrees i hi⟩
#print axioms constructed
end R1Z.PV_OWND_ActualInitialized

import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_Kind10
open PV_OWN_Link PV_OWNB_KindCodec
/-- Active-field read for variant 10; no constraint on padding bytes. -/
theorem read (raw : Nat → Option UInt8)
 (h0:raw 0=some (10:UInt8)) :
 decode raw=some (Kind.conservationRecipient) := by
 simp [decode,h0]
#print axioms read
end R1Z.PV_OWNB_Kind10

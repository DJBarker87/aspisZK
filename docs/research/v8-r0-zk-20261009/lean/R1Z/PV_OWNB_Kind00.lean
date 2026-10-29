import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_Kind00
open PV_OWN_Link PV_OWNB_KindCodec
/-- Active-field read for variant 0; no constraint on padding bytes. -/
theorem read (raw : Nat → Option UInt8) (a b : UInt8)
 (h0:raw 0=some (0:UInt8)) (h1:raw 1=some a)
 (h2:raw 2=some b) :
 decode raw=some (Kind.spongeCarry a b) := by
 simp [decode,h0,h1,h2]
#print axioms read
end R1Z.PV_OWNB_Kind00

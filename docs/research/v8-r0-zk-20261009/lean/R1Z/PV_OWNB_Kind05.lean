import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_Kind05
open PV_OWN_Link PV_OWNB_KindCodec
/-- Active-field read for variant 5; no constraint on padding bytes. -/
theorem read (raw : Nat → Option UInt8) (a : UInt8)
 (h0:raw 0=some (5:UInt8)) (h1:raw 1=some a) :
 decode raw=some (Kind.privatePathCurrent a) := by
 simp [decode,h0,h1]
#print axioms read
end R1Z.PV_OWNB_Kind05

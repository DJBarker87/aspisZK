import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_Kind16
open PV_OWN_Link PV_OWNB_KindCodec
/-- Active-field read for variant 16; no constraint on padding bytes. -/
theorem read (raw : Nat → Option UInt8)
 (h0:raw 0=some (16:UInt8)) :
 decode raw=some (Kind.outputPairFirst) := by
 simp [decode,h0]
#print axioms read
end R1Z.PV_OWNB_Kind16

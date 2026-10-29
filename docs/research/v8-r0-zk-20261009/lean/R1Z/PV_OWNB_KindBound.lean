import R1Z.PV_OWNB_KindCodec
set_option autoImplicit false
namespace R1Z.PV_OWNB_KindBound
open PV_OWN_Link PV_OWNB_KindCodec
theorem bounded (k : Kind) (i : Nat) (b : UInt8) (h:encode k i=some b) : i<3 := by
 by_contra hn
 have h0:i≠0 := by omega
 have h1:i≠1 := by omega
 have h2:i≠2 := by omega
 simp [encode,h0,h1,h2] at h
#print axioms bounded
end R1Z.PV_OWNB_KindBound

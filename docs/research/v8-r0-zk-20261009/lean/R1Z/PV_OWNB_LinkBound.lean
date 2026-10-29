import R1Z.PV_OWNB_LinkBytes
set_option autoImplicit false
namespace R1Z.PV_OWNB_LinkBound
open PV_OWN_Link PV_OWNB_LinkBytes
theorem bounded (v : Link) (i : Nat) (b : UInt8) (h:encode v i=some b) : i<8 := by
 by_cases hn:i<8
 · exact hn
 ·
   have hi:7≤i := by omega
   rw [trailing_padding v i hi] at h
   cases h
#print axioms bounded
end R1Z.PV_OWNB_LinkBound

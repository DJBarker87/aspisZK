import R1Z.PV_OWNB_KindCodec
import R1Z.PV_OWN_U16
set_option autoImplicit false
namespace R1Z.PV_OWNB_LinkBytes
open PV_OWN_Link PV_OWN_Bytes
/-- Eight-byte candidate ABI representation; only active fields initialized. -/
def encode (v : Link) : Bytes := fun i =>
 if i<2 then PV_OWN_U16.encode v.producer i else
 if i<4 then PV_OWN_U16.encode v.consumer (i-2) else
 if i<7 then PV_OWNB_KindCodec.encode v.kind (i-4) else none

theorem producer (v : Link) (i : Nat) (h:i<2) :
 encode v i=PV_OWN_U16.encode v.producer i := by simp [encode,h]
theorem consumer (v : Link) (i : Nat) (h:i<2) :
 encode v (2+i)=PV_OWN_U16.encode v.consumer i := by
 simp [encode,show ¬2+i<2 by omega,show 2+i<4 by omega]
theorem kind (v : Link) (i : Nat) (h:i<3) :
 encode v (4+i)=PV_OWNB_KindCodec.encode v.kind i := by
 simp [encode,show ¬4+i<2 by omega,show ¬4+i<4 by omega,show 4+i<7 by omega]
theorem trailing_padding (v : Link) (i : Nat) (h:7≤i) : encode v i=none := by
 simp [encode,show ¬i<2 by omega,show ¬i<4 by omega,show ¬i<7 by omega]
attribute [irreducible] encode
#print axioms producer
#print axioms consumer
#print axioms kind
#print axioms trailing_padding
end R1Z.PV_OWNB_LinkBytes

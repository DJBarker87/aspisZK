import R1Z.PV_OWNB_LinkBytes
import R1Z.PV_OWNB_KindAgreement
import R1Z.PV_OWNB_KindBound
set_option autoImplicit false
namespace R1Z.PV_OWNB_LinkFields
open PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding
/-- Project field agreement from the actual eight-byte object. -/
theorem producer (v : Link) (raw : Bytes)
 (h:Agrees (PV_OWNB_LinkBytes.encode v) raw) :
 Agrees (PV_OWN_U16.encode v.producer) (fun i => raw i) := by
 intro i b hi
 by_cases hh:i<2
 · exact h i b ((PV_OWNB_LinkBytes.producer v i hh).trans hi)
 · have h0:i≠0 := by omega
   have h1:i≠1 := by omega
   simp [PV_OWN_U16.encode,h0,h1] at hi

theorem consumer (v : Link) (raw : Bytes)
 (h:Agrees (PV_OWNB_LinkBytes.encode v) raw) :
 Agrees (PV_OWN_U16.encode v.consumer) (fun i => raw (2+i)) := by
 intro i b hi
 by_cases hh:i<2
 · exact h (2+i) b ((PV_OWNB_LinkBytes.consumer v i hh).trans hi)
 · have h0:i≠0 := by omega
   have h1:i≠1 := by omega
   simp [PV_OWN_U16.encode,h0,h1] at hi

theorem kind (v : Link) (raw : Bytes)
 (h:Agrees (PV_OWNB_LinkBytes.encode v) raw) :
 Agrees (PV_OWNB_KindCodec.encode v.kind) (fun i => raw (4+i)) := by
 intro i b hi
 have hh:=PV_OWNB_KindBound.bounded v.kind i b hi
 exact h (4+i) b ((PV_OWNB_LinkBytes.kind v i hh).trans hi)
#print axioms producer
#print axioms consumer
#print axioms kind
end R1Z.PV_OWNB_LinkFields

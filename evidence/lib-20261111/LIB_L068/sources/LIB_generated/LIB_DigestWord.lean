import LIB_Carriers
import NFY_Part005
import NND_Carrier
import RSL_TX2_217
set_option autoImplicit false
namespace LIB_DigestWord
open Aeneas Aeneas.Std
#print BitVec.fromLEBytes
/-- Four symbolic bytes; the primitive little-endian carrier association. -/
theorem four (a b c d : U8) :
 NND_Carrier.word (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) =
 RSL.le32 (NND_Carrier.byte a) (NND_Carrier.byte b)
   (NND_Carrier.byte c) (NND_Carrier.byte d) := by
 apply UInt32.toBitVec_inj.mp
 simp only [core.num.U32.from_le_bytes,Array.make,NND_Carrier.word,NND_Carrier.byte,
   RSL.le32,BitVec.fromLEBytes,List.map_cons,List.map_nil]
 bv_decide
#print axioms four
end LIB_DigestWord

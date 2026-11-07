import NMX_R3_RawWord32Byte0
import NMX_R3_RawWord32Byte1
import NMX_R3_RawWord32Byte2
import NMX_R3_RawWord32Byte3
set_option autoImplicit false
namespace NMX_R3_RawWord32
open NMX_R3_RawWord32Defs
theorem value (a b c d : BitVec 8) : encoded a b c d = assembled a b c d := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 by_cases h0 : i < 8
 · exact NMX_R3_RawWord32Byte0.value a b c d i (by omega) h0
 by_cases h1 : i < 16
 · exact NMX_R3_RawWord32Byte1.value a b c d i (by omega) h1
 by_cases h2 : i < 24
 · exact NMX_R3_RawWord32Byte2.value a b c d i (by omega) h2
 · exact NMX_R3_RawWord32Byte3.value a b c d i (by omega) hi
#print axioms value
end NMX_R3_RawWord32

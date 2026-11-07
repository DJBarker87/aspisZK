import NMX_R3_RawWord64Byte0
import NMX_R3_RawWord64Byte1
import NMX_R3_RawWord64Byte2
import NMX_R3_RawWord64Byte3
import NMX_R3_RawWord64Byte4
import NMX_R3_RawWord64Byte5
import NMX_R3_RawWord64Byte6
import NMX_R3_RawWord64Byte7
set_option autoImplicit false
namespace NMX_R3_RawWord64
open NMX_R3_RawWord64Defs
theorem value (v : Fin 8 → BitVec 8) : encoded v = folded v := by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 by_cases h0 : i < 8
 · exact NMX_R3_RawWord64Byte0.value v i (by omega) h0
 by_cases h1 : i < 16
 · exact NMX_R3_RawWord64Byte1.value v i (by omega) h1
 by_cases h2 : i < 24
 · exact NMX_R3_RawWord64Byte2.value v i (by omega) h2
 by_cases h3 : i < 32
 · exact NMX_R3_RawWord64Byte3.value v i (by omega) h3
 by_cases h4 : i < 40
 · exact NMX_R3_RawWord64Byte4.value v i (by omega) h4
 by_cases h5 : i < 48
 · exact NMX_R3_RawWord64Byte5.value v i (by omega) h5
 by_cases h6 : i < 56
 · exact NMX_R3_RawWord64Byte6.value v i (by omega) h6
 exact NMX_R3_RawWord64Byte7.value v i (by omega) hi
#print axioms value
end NMX_R3_RawWord64

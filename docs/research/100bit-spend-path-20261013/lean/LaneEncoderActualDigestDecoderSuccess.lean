import AspisR1TerminalDecoder.Funs
import LaneEncoderByteGetterBridge
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualDigestDecoderSuccess
open Aeneas Aeneas.Std Result

theorem successful_decode_digest_of_chunks
    (bytes : Array U8 32#usize) (x0 x1 x2 x3 x4 x5 x6 x7 : U32)
    (h0 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[0]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[1]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[2]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[3]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x0))
    (h1 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[4]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[5]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[6]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[7]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x1))
    (h2 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[8]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[9]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[10]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[11]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x2))
    (h3 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[12]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[13]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[14]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[15]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x3))
    (h4 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[16]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[17]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[18]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[19]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x4))
    (h5 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[20]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[21]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[22]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[23]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x5))
    (h6 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[24]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[25]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[26]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[27]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x6))
    (h7 : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes (Array.make 4#usize [bytes.val[28]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[29]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[30]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega), bytes.val[31]'(by have h := bytes.property; change bytes.val.length = 32 at h; omega)]) = .ok (some x7)) :
    AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes =
      .ok (.Ok (Array.make 8#usize [x0,x1,x2,x3,x4,x5,x6,x7])) := by
  simp only [Array.make] at h0 h1 h2 h3 h4 h5 h6 h7
  have hbytesLen : bytes.val.length = 32 := by
    have h := bytes.property
    change bytes.val.length = 32 at h
    exact h
  have hb0 : bytes.val[0]'(by omega) = (↑bytes)[0]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 0 (by omega)
  have hb1 : bytes.val[1]'(by omega) = (↑bytes)[1]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 1 (by omega)
  have hb2 : bytes.val[2]'(by omega) = (↑bytes)[2]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 2 (by omega)
  have hb3 : bytes.val[3]'(by omega) = (↑bytes)[3]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 3 (by omega)
  simp only [hb0, hb1, hb2, hb3] at h0
  have hb4 : bytes.val[4]'(by omega) = (↑bytes)[4]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 4 (by omega)
  have hb5 : bytes.val[5]'(by omega) = (↑bytes)[5]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 5 (by omega)
  have hb6 : bytes.val[6]'(by omega) = (↑bytes)[6]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 6 (by omega)
  have hb7 : bytes.val[7]'(by omega) = (↑bytes)[7]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 7 (by omega)
  simp only [hb4, hb5, hb6, hb7] at h1
  have hb8 : bytes.val[8]'(by omega) = (↑bytes)[8]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 8 (by omega)
  have hb9 : bytes.val[9]'(by omega) = (↑bytes)[9]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 9 (by omega)
  have hb10 : bytes.val[10]'(by omega) = (↑bytes)[10]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 10 (by omega)
  have hb11 : bytes.val[11]'(by omega) = (↑bytes)[11]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 11 (by omega)
  simp only [hb8, hb9, hb10, hb11] at h2
  have hb12 : bytes.val[12]'(by omega) = (↑bytes)[12]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 12 (by omega)
  have hb13 : bytes.val[13]'(by omega) = (↑bytes)[13]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 13 (by omega)
  have hb14 : bytes.val[14]'(by omega) = (↑bytes)[14]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 14 (by omega)
  have hb15 : bytes.val[15]'(by omega) = (↑bytes)[15]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 15 (by omega)
  simp only [hb12, hb13, hb14, hb15] at h3
  have hb16 : bytes.val[16]'(by omega) = (↑bytes)[16]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 16 (by omega)
  have hb17 : bytes.val[17]'(by omega) = (↑bytes)[17]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 17 (by omega)
  have hb18 : bytes.val[18]'(by omega) = (↑bytes)[18]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 18 (by omega)
  have hb19 : bytes.val[19]'(by omega) = (↑bytes)[19]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 19 (by omega)
  simp only [hb16, hb17, hb18, hb19] at h4
  have hb20 : bytes.val[20]'(by omega) = (↑bytes)[20]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 20 (by omega)
  have hb21 : bytes.val[21]'(by omega) = (↑bytes)[21]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 21 (by omega)
  have hb22 : bytes.val[22]'(by omega) = (↑bytes)[22]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 22 (by omega)
  have hb23 : bytes.val[23]'(by omega) = (↑bytes)[23]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 23 (by omega)
  simp only [hb20, hb21, hb22, hb23] at h5
  have hb24 : bytes.val[24]'(by omega) = (↑bytes)[24]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 24 (by omega)
  have hb25 : bytes.val[25]'(by omega) = (↑bytes)[25]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 25 (by omega)
  have hb26 : bytes.val[26]'(by omega) = (↑bytes)[26]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 26 (by omega)
  have hb27 : bytes.val[27]'(by omega) = (↑bytes)[27]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 27 (by omega)
  simp only [hb24, hb25, hb26, hb27] at h6
  have hb28 : bytes.val[28]'(by omega) = (↑bytes)[28]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 28 (by omega)
  have hb29 : bytes.val[29]'(by omega) = (↑bytes)[29]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 29 (by omega)
  have hb30 : bytes.val[30]'(by omega) = (↑bytes)[30]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 30 (by omega)
  have hb31 : bytes.val[31]'(by omega) = (↑bytes)[31]'(by omega) := by
    exact AspisR1PairForestLaneEncoderTailByteGetterBridge.arrayGet_eq_sliceGet bytes 31 (by omega)
  simp only [hb28, hb29, hb30, hb31] at h7
  simp only [← hb0, ← hb1, ← hb2, ← hb3, ← hb4, ← hb5, ← hb6, ← hb7, ← hb8, ← hb9, ← hb10, ← hb11, ← hb12, ← hb13, ← hb14, ← hb15, ← hb16, ← hb17, ← hb18, ← hb19, ← hb20, ← hb21, ← hb22, ← hb23, ← hb24, ← hb25, ← hb26, ← hb27, ← hb28, ← hb29, ← hb30, ← hb31] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical,
    Array.index_usize, Array.make, AspisR1TerminalDecoder.core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, h0, h1, h2, h3, h4, h5, h6, h7, bind_tc_ok]

#print axioms successful_decode_digest_of_chunks
end AspisR1PairForestLaneEncoderTailActualDigestDecoderSuccess

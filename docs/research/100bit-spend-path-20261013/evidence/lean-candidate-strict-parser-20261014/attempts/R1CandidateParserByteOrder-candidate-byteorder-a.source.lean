import R1CandidateQM31Parser

/-! Byte-position identities connecting the candidate array slices to the
    retained QM31 limb order. -/
set_option autoImplicit false

namespace AspisR1.CandidateParserByteOrder

open Aeneas Aeneas.Std
open AspisR1.RetainedFieldByteCodec

def arrayBytes16 (arr : Array U8 16#usize) : QM31Bytes :=
  fun i => AspisV8R19.SqueezeOracleBridge.decodeByte
    (arr.val[i.val]'(by
      have hlen := arr.property
      change arr.val.length = 16 at hlen
      omega))

theorem half00_bytes (arr : Array U8 16#usize) :
    AspisR1.M31ParserArray.arrayBytes
        (AspisR1.CandidateCM31Parser.half0
          (AspisR1.CandidateQM31Parser.half0 arr)) =
      qm31LimbBytes (arrayBytes16 arr) 0 := by
  funext byte
  apply Fin.ext
  simp [AspisR1.M31ParserArray.arrayBytes, arrayBytes16,
    AspisR1.CandidateCM31Parser.half0,
    AspisR1.CandidateQM31Parser.half0,
    AspisR1.ParserArraySlice.segment,
    qm31LimbBytes, limbByteIndex_val, limbByteIndex]

theorem half10_bytes (arr : Array U8 16#usize) :
    AspisR1.M31ParserArray.arrayBytes
        (AspisR1.CandidateCM31Parser.half1
          (AspisR1.CandidateQM31Parser.half0 arr)) =
      qm31LimbBytes (arrayBytes16 arr) 1 := by
  funext byte
  apply Fin.ext
  simp [AspisR1.M31ParserArray.arrayBytes, arrayBytes16,
    AspisR1.CandidateCM31Parser.half1,
    AspisR1.CandidateQM31Parser.half0,
    AspisR1.ParserArraySlice.segment,
    qm31LimbBytes, limbByteIndex_val, limbByteIndex]

theorem half01_bytes (arr : Array U8 16#usize) :
    AspisR1.M31ParserArray.arrayBytes
        (AspisR1.CandidateCM31Parser.half0
          (AspisR1.CandidateQM31Parser.half1 arr)) =
      qm31LimbBytes (arrayBytes16 arr) 2 := by
  funext byte
  apply Fin.ext
  simp [AspisR1.M31ParserArray.arrayBytes, arrayBytes16,
    AspisR1.CandidateCM31Parser.half0,
    AspisR1.CandidateQM31Parser.half1,
    AspisR1.ParserArraySlice.segment,
    qm31LimbBytes, limbByteIndex_val, limbByteIndex]

theorem half11_bytes (arr : Array U8 16#usize) :
    AspisR1.M31ParserArray.arrayBytes
        (AspisR1.CandidateCM31Parser.half1
          (AspisR1.CandidateQM31Parser.half1 arr)) =
      qm31LimbBytes (arrayBytes16 arr) 3 := by
  funext byte
  apply Fin.ext
  simp [AspisR1.M31ParserArray.arrayBytes, arrayBytes16,
    AspisR1.CandidateCM31Parser.half1,
    AspisR1.CandidateQM31Parser.half1,
    AspisR1.ParserArraySlice.segment,
    qm31LimbBytes, limbByteIndex_val, limbByteIndex]

#print axioms half00_bytes
#print axioms half10_bytes
#print axioms half01_bytes
#print axioms half11_bytes

end AspisR1.CandidateParserByteOrder

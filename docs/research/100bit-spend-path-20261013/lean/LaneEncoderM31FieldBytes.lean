import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import LaneEncoderM31CodecRoundtrip
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailM31FieldBytes
open Aeneas Aeneas.Std

theorem m31_source_bytes_decode (x : AspisR1PairForestLaneEncoderTailSourceCut.M31) :
    ∃ bytes : Array U8 4#usize,
      AspisR1PairForestLaneEncoderTailSourceCut.M31.to_le_bytes x = .ok bytes ∧
      core.num.U32.from_le_bytes bytes = x := by
  refine ⟨core.num.U32.to_le_bytes x, ?_, ?_⟩
  · rfl
  · exact AspisR1PairForestLaneEncoderTailM31Codec.u32_from_to_le x

#print axioms m31_source_bytes_decode
end AspisR1PairForestLaneEncoderTailM31FieldBytes

import LaneEncoderM31ParserAcceptEncoded
import LaneEncoderChunkArrayEquality
import AspisR1TerminalDecoder.Funs
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualDigestChunkParser
open Aeneas Aeneas.Std Result

theorem actual_m31_parser_accepts_window
    (out : Array U8 32#usize) (offset : Nat)
    (hoff : offset + 4 ≤ 32) (value : U32)
    (hwindow : ∀ k : Nat, (hk : k < 4) →
      out.val[offset + k]'(by
        have hlen : out.val.length = 32 := by
          have h := out.property
          change out.val.length = 32 at h
          exact h
        rw [hlen]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk offset) hoff) =
      (core.num.U32.to_le_bytes value).val[k]'(by
        have hlen : (core.num.U32.to_le_bytes value).val.length = 4 := by
          have h := (core.num.U32.to_le_bytes value).property
          change (core.num.U32.to_le_bytes value).val.length = 4 at h
          exact h
        rw [hlen]
        exact hk))
    (hcanonical : value.val < 2147483647) :
    AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk out offset hoff) =
        .ok (some value) := by
  have hmake :
      AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk out offset hoff =
        core.num.U32.to_le_bytes value := by
    exact AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk_eq_of_getElem?
      out (core.num.U32.to_le_bytes value) offset hoff hwindow
  rw [hmake]
  exact AspisR1PairForestLaneEncoderTailM31ParserAcceptEncoded.actual_parser_accepts_encoded
    value hcanonical


theorem actual_m31_parser_accepts_window_getElem?
    (out : Array U8 32#usize) (offset : Nat)
    (hoff : offset + 4 ≤ 32) (value : U32)
    (hwindow : ∀ k : Nat, k < 4 →
      out.val[offset + k]? = (core.num.U32.to_le_bytes value).val[k]?)
    (hcanonical : value.val < 2147483647) :
    AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes
      (AspisR1PairForestLaneEncoderTailChunkArrayEquality.makeChunk out offset hoff) =
        .ok (some value) := by
  apply actual_m31_parser_accepts_window out offset hoff value ?_ hcanonical
  intro k hk
  have hlenOut : out.val.length = 32 := by
    have h := out.property
    change out.val.length = 32 at h
    exact h
  have hlenEncoded : (core.num.U32.to_le_bytes value).val.length = 4 := by
    have h := (core.num.U32.to_le_bytes value).property
    change (core.num.U32.to_le_bytes value).val.length = 4 at h
    exact h
  have hleft : offset + k < out.val.length := by rw [hlenOut]; omega
  have hright : k < (core.num.U32.to_le_bytes value).val.length := by rw [hlenEncoded]; exact hk
  have hopt := hwindow k hk
  have hlist : out.val[offset + k]? = (core.num.U32.to_le_bytes value).val[k]? := by
    simpa only [Aeneas.Std.Slice.getElem?_Nat_eq] using hopt
  have hdirect : some (out.val[offset + k]'(hleft)) =
      some ((core.num.U32.to_le_bytes value).val[k]'(hright)) := by
    simpa only [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] using hlist
  exact Option.some.inj hdirect


#print axioms actual_m31_parser_accepts_window
end AspisR1PairForestLaneEncoderTailActualDigestChunkParser

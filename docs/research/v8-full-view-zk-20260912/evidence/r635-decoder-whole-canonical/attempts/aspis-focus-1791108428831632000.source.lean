import AspisV8R19.R623PackedDecoderExecution

set_option autoImplicit false

namespace AspisV8R19.R636DecoderAcceptedHeader

open Aeneas Aeneas.Std Result
open Aeneas.Std.WP
open AspisV8R19.R623PackedDecoderExecution

/-- A successful actual selected packed decoder call passes the outer header
checks.  This records only the accepted header consequences; the loop body is
reused through `decoder_complete`. -/
theorem accepted_header {N : Usize} (hN : N.val ≤ 104) (bytes : Slice U8)
    (out out1 : Array U32 N)
    (h : AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into bytes out =
      .ok (core.result.Result.Ok (), out1)) :
    0 < N.val ∧ N.val % 8 = 0 ∧ bytes.val.length = 31 * (N.val / 8) := by
  rw [decoder_complete] at h
  unfold packedDecoder at h
  split at h <;> rename_i hz
  · simp at h
  · split at h <;> rename_i hr
    · simp at h
    · simp only [bind_tc_bind, bind_tc_ok] at h
      split at h <;> rename_i hlen
      · simp at h
      · simp only [bind_tc_bind, bind_tc_ok] at h
        split at h <;> simp at h
        · exact False.elim (by contradiction)
        · sorry

#print axioms accepted_header
end AspisV8R19.R636DecoderAcceptedHeader

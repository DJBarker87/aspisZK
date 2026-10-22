import Query31UnrolledDriverFirstStop
import Query31ExplicitScanBody

open Aeneas Aeneas.Std
set_option autoImplicit false

namespace AspisR1QueryFinishAcceptedBridgeV1

/-- Successful QueryScan.finish returns exactly the accepted U32 words, and
    q22StateOf exposes those words as their natural values. -/
theorem finish_success_accepted_values
    (s : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan)
    (out : Array Std.U32 22#usize)
    (hfinish : AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish s =
      .ok (.Ok out)) :
    out.val.map (fun w => w.val) =
      (Query31ExplicitScanBody.q22StateOf s).accepted := by
  have hsuccess :=
    (AspisR1Query31Transcript.finish_success_iff s out).mp hfinish
  rcases hsuccess with ⟨hlen, hout⟩
  subst out
  have hcount : s.accepted_len.val = 22 := by
    have h := congrArg UScalar.val hlen
    have hq : AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT.val = 22 := by
      unfold AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT
      scalar_tac
    simpa [hq] using h
  have hlength : s.accepted.val.length = 22 := by
    have h := s.accepted.property
    have hq : (22#usize : Usize).val = 22 := by scalar_tac
    simpa [hq] using h
  have htake : s.accepted.val.take s.accepted_len.val = s.accepted.val := by
    rw [hcount]
    exact List.take_of_length_le (by omega)
  change s.accepted.val.map (fun w => w.val) =
    (s.accepted.val.take s.accepted_len.val).map (fun w => w.val)
  rw [htake]

#print axioms finish_success_accepted_values

end AspisR1QueryFinishAcceptedBridgeV1

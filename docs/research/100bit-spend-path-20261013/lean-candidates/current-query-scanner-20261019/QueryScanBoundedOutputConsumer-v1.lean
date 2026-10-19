import QueryScanActualScanBridge
import QueryWordsRange
import AspisR1QueryScan.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

theorem queryscan_actual_success_bounded_q22
    (s : QueryScan) (block : Array Std.U8 32#usize) (stopped : Bool) (sf : QueryScan)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
    (hscan : QueryScan.scan s block = .ok (stopped, sf)) :
    ∃ words : Array Std.U32 8#usize,
      query_words block = .ok words ∧
      (∀ w ∈ words.val, w.val < 262144) ∧
      scan (q22StateOfFresh s) (words.val.map (fun x => x.val)) =
        (q22StateOfFresh sf, stopped) ∧
      sf.accepted_len.val ≤ 22 ∧ sf.draws.val ≤ 64 := by
  obtain ⟨words, hwords, hmodel, hlen', hdraw'⟩ :=
    queryscan_actual_success_q22 s block stopped sf hlen hdraw hscan
  exact ⟨words, hwords, AspisR1QueryScanUnrolled.query_words_success_range block words hwords,
    hmodel, hlen', hdraw'⟩

#print axioms queryscan_actual_success_bounded_q22
end AspisR1QueryScanUnrolled.r0_transcript

import QueryScanEightBlockHandoff
import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

theorem queryscan_actual_success_q22
    (s : QueryScan) (block : Array Std.U8 32#usize) (stopped : Bool) (sf : QueryScan)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64)
    (hscan : QueryScan.scan s block = .ok (stopped, sf)) :
    ∃ words : Array Std.U32 8#usize,
      query_words block = .ok words ∧
      scan (q22StateOfFresh s) (words.val.map (fun x => x.val)) =
        (q22StateOfFresh sf, stopped) ∧
      sf.accepted_len.val ≤ 22 ∧ sf.draws.val ≤ 64 := by
  have hwords : ∃ words : Array Std.U32 8#usize, query_words block = .ok words := by
    unfold QueryScan.scan at hscan
    cases hq : query_words block with
    | ok words => exact ⟨words, rfl⟩
    | fail e => simp [hq] at hscan
    | div => simp [hq] at hscan
  obtain ⟨words, hwords⟩ := hwords
  obtain ⟨sf0, stopped0, hsource, hmodel, hlen0, hdraw0⟩ :=
    queryScan_scan_q22_of_queryWords s block words hlen hdraw hwords
  have hp : (stopped0, sf0) = (stopped, sf) := Result.ok.inj (hsource.symm.trans hscan)
  rcases hp with ⟨rfl, rfl⟩
  exact ⟨words, hwords, hmodel, hlen0, hdraw0⟩

#print axioms queryscan_actual_success_q22
end AspisR1QueryScanUnrolled.r0_transcript

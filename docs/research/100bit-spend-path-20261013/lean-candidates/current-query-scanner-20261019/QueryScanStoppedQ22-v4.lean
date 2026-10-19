import AspisR1QueryScan.Funs
import AspisV8R19.Q22WordScan
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

def q22StateOf (s : QueryScan) : ScanState :=
  ⟨(s.accepted.val.take s.accepted_len.val).map (fun x => x.val), s.draws.val⟩

theorem q22StateOf_stopped_of_source_stop (s : QueryScan)
    (hstop : s.accepted_len = QUERY_COUNT ∨ s.draws = QUERY_MAX_DRAWS) :
    (q22StateOf s).accepted.length = 22 ∨ (q22StateOf s).draws = 64 := by
  rcases hstop with hlen | hdraw
  · left
    have hlenval : s.accepted_len.val = 22 := by
      simpa [QUERY_COUNT] using congrArg UScalar.val hlen
    simp [q22StateOf, hlenval, s.accepted.property]
  · right
    have hdrawval : s.draws.val = 64 := by
      simpa [QUERY_MAX_DRAWS] using congrArg UScalar.val hdraw
    exact hdrawval

theorem scan_loop_stopped_q22 (s : QueryScan) (x : Std.U32)
    (xs : List Std.U32) (q : ScanState) (hq : q = q22StateOf s)
    (hstop : s.accepted_len = QUERY_COUNT ∨ s.draws = QUERY_MAX_DRAWS) :
    QueryScan.scan_loop (x :: xs) s = .ok (s, none) ∧
      scan q ((x :: xs).map (fun x => x.val)) = (q, true) := by
  have hqstop := q22StateOf_stopped_of_source_stop s hstop
  subst q
  constructor
  · unfold QueryScan.scan_loop
    rw [loop.eq_def]
    rcases hstop with hlen | hdraw
    · simp [QueryScan.scan_loop.body,
        core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
        hlen, TerminalV4ArrayIntoIterListModel.next]
    · by_cases hlen : s.accepted_len = QUERY_COUNT
      · simp [QueryScan.scan_loop.body,
          core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
          hlen, TerminalV4ArrayIntoIterListModel.next]
      · simp [QueryScan.scan_loop.body,
          core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
          hlen, hdraw, TerminalV4ArrayIntoIterListModel.next]
  · simp [scan, hqstop]

#print axioms q22StateOf_stopped_of_source_stop
#print axioms scan_loop_stopped_q22
end AspisR1QueryScanUnrolled.r0_transcript

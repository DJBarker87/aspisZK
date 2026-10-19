import QueryScanBoundedDuplicate
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

theorem scan_loop_cons_unroll
    (x : Std.U32) (xs : List Std.U32) (s s' : QueryScan)
    (hbody : QueryScan.scan_loop.body (x :: xs) s =
      .ok (.cont (xs, s'))) :
    QueryScan.scan_loop (x :: xs) s = QueryScan.scan_loop xs s' := by
  unfold QueryScan.scan_loop
  rw [loop.eq_def]
  dsimp
  rw [hbody]

theorem scan_loop_empty (s : QueryScan) :
    QueryScan.scan_loop ([] : List Std.U32) s = .ok (s, some false) := by
  unfold QueryScan.scan_loop
  rw [loop.eq_def]
  simp [QueryScan.scan_loop.body,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    TerminalV4ArrayIntoIterListModel.next]

theorem q22_scan_cons_fresh_unroll
    (q : ScanState) (x : Nat) (xs : List Nat)
    (hactive : q.accepted.length ≠ 22 ∧ q.draws ≠ 64)
    (hfresh : x ∉ q.accepted) :
    scan q (x :: xs) = scan ⟨q.accepted ++ [x], q.draws + 1⟩ xs := by
  simp [scan, keep, hactive.1, hactive.2, hfresh]

theorem q22_scan_cons_duplicate_unroll
    (q : ScanState) (x : Nat) (xs : List Nat)
    (hactive : q.accepted.length ≠ 22 ∧ q.draws ≠ 64)
    (hmember : x ∈ q.accepted) :
    scan q (x :: xs) = scan ⟨q.accepted, q.draws + 1⟩ xs := by
  simp [scan, keep, hactive.1, hactive.2, hmember]

#print axioms scan_loop_cons_unroll
#print axioms scan_loop_empty
#print axioms q22_scan_cons_fresh_unroll
#print axioms q22_scan_cons_duplicate_unroll
end AspisR1QueryScanUnrolled.r0_transcript

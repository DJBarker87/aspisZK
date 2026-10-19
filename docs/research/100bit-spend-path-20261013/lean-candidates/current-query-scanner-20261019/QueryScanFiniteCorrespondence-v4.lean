import QueryScanFiniteRecurrence
import QueryScanStoppedQ22
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

def q22Option (b : Bool) : Option Bool := if b then none else some false

theorem queryscan_q22_finite_correspondence (s : QueryScan)
    (xs : List Std.U32)
    (hlen : s.accepted_len.val ≤ 22) (hdraw : s.draws.val ≤ 64) :
    ∃ sf stopped,
      QueryScan.scan_loop xs s = .ok (sf, q22Option stopped) ∧
      scan (q22StateOfFresh s) (xs.map (fun x => x.val)) =
        (q22StateOfFresh sf, stopped) := by
  induction xs generalizing s with
  | nil =>
      refine ⟨s, false, scan_loop_empty s, ?_⟩
      simp [q22Option, scan]
  | cons x xs ih =>
      by_cases hstop : s.accepted_len = QUERY_COUNT ∨ s.draws = QUERY_MAX_DRAWS
      · obtain ⟨hsource, hmodel⟩ :=
          scan_loop_stopped_q22 s x xs (q22StateOfFresh s) rfl hstop
        exact ⟨s, true, by simpa [q22Option] using hsource, by simpa using hmodel⟩
      · have hlenLt : s.accepted_len.val < 22 := by
          by_contra hnot
          have hv : s.accepted_len.val = QUERY_COUNT.val := by
            simp [QUERY_COUNT]
            omega
          exact hstop (Or.inl (UScalar.eq_of_val_eq hv))
        have hdrawLt : s.draws.val < 64 := by
          by_contra hnot
          have hv : s.draws.val = QUERY_MAX_DRAWS.val := by
            simp [QUERY_MAX_DRAWS]
            omega
          exact hstop (Or.inr (UScalar.eq_of_val_eq hv))
        have hactive := active_q22_of_bounded_source s hlenLt hdrawLt
        have hnext :
            @core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next U32 (8#usize) (x :: xs) =
              ok (some x, xs) := by
          rfl
        by_cases hfresh : x.val ∉ acceptedPrefix s
        · obtain ⟨drawNext, lenNext, a, hdrawOp, hdrawVal, hlenOp, hlenVal,
              hupdate, hbody, hstate⟩ :=
            scan_body_fresh_from_bounds (x :: xs) s x xs hnext hlenLt hdrawLt hfresh
          let s' : QueryScan := { s with accepted := a, accepted_len := lenNext, draws := drawNext }
          have hlen' : s'.accepted_len.val ≤ 22 := by simp [s', hlenVal]; omega
          have hdraw' : s'.draws.val ≤ 64 := by simp [s', hdrawVal]; omega
          obtain ⟨sf, stopped, hsourceTail, hmodelTail⟩ := ih s' hlen' hdraw'
          have hunroll := scan_loop_cons_unroll x xs s s' hbody
          have hmodelStep := q22_scan_cons_fresh_unroll (q22StateOfFresh s) x.val
            (xs.map (fun y => y.val)) hactive hfresh
          have hmodelStep' : scan (q22StateOfFresh s) (x.val :: xs.map (fun y => y.val)) =
              scan (⟨acceptedPrefix s ++ [x.val], s.draws.val + 1⟩ : ScanState)
                (xs.map (fun y => y.val)) := by
            simpa [q22StateOfFresh] using hmodelStep
          refine ⟨sf, stopped, ?_, ?_⟩
          · rw [hunroll, hsourceTail]
          · rw [List.map_cons]
            rw [hmodelStep', ← hstate, hmodelTail]
        · have hmember : x.val ∈ acceptedPrefix s := by
            by_contra hmem
            exact hfresh hmem
          obtain ⟨drawNext, hdrawOp, hdrawVal, hbody, hstate⟩ :=
            scan_body_duplicate_from_bounds (x :: xs) s x xs hnext hlenLt hdrawLt hmember
          let s' : QueryScan := { s with draws := drawNext }
          have hlen' : s'.accepted_len.val ≤ 22 := by simpa [s'] using hlen
          have hdraw' : s'.draws.val ≤ 64 := by simp [s', hdrawVal]; omega
          obtain ⟨sf, stopped, hsourceTail, hmodelTail⟩ := ih s' hlen' hdraw'
          have hunroll := scan_loop_cons_unroll x xs s s' hbody
          have hmodelStep := q22_scan_cons_duplicate_unroll (q22StateOfFresh s) x.val
            (xs.map (fun y => y.val)) hactive hmember
          have hmodelStep' : scan (q22StateOfFresh s) (x.val :: xs.map (fun y => y.val)) =
              scan (⟨acceptedPrefix s, s.draws.val + 1⟩ : ScanState)
                (xs.map (fun y => y.val)) := by
            simpa [q22StateOfFresh] using hmodelStep
          refine ⟨sf, stopped, ?_, ?_⟩
          · rw [hunroll, hsourceTail]
          · rw [List.map_cons]
            rw [hmodelStep', ← hstate, hmodelTail]

#print axioms queryscan_q22_finite_correspondence
end AspisR1QueryScanUnrolled.r0_transcript

import QueryScanBoundedBody
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript
open AspisV8R19.Q22WordScan

private theorem not_query_count_of_lt_dup (s : QueryScan) (h : s.accepted_len.val < 22) :
    s.accepted_len ≠ QUERY_COUNT := by
  intro he
  have hv := congrArg UScalar.val he
  simp [QUERY_COUNT] at hv
  omega

private theorem not_query_cap_of_lt_dup (s : QueryScan) (h : s.draws.val < 64) :
    s.draws ≠ QUERY_MAX_DRAWS := by
  intro he
  have hv := congrArg UScalar.val he
  simp [QUERY_MAX_DRAWS] at hv
  omega

private theorem slice_read_prefix_success_dup (s : QueryScan)
    (hlen : s.accepted_len.val < 22) :
    ∃ sl : Slice Std.U32,
      core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
        s.accepted { «end» := s.accepted_len } = .ok sl ∧
      (↑sl : List Std.U32) = s.accepted.val.take s.accepted_len.val := by
  have h22 : (22#usize).val = 22 := rfl
  have hbound : s.accepted_len.val ≤ (s.accepted : Array Std.U32 22#usize).length := by
    simp only [Array.length, s.accepted.property, h22]
    omega
  have hs := core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    ({ «end» := s.accepted_len } : core.ops.range.RangeTo Std.Usize)
    (Array.to_slice s.accepted) hbound
  obtain ⟨sl, hrun, hspec⟩ := Aeneas.Std.WP.spec_imp_exists hs
  refine ⟨sl, ?_, ?_⟩
  · change core.slice.index.SliceIndexRangeToUsizeSlice.index
      { «end» := s.accepted_len } (Array.to_slice s.accepted) = .ok sl
    exact hrun
  · rcases hspec with ⟨hv, _⟩
    simpa [Array.to_slice, List.slice] using hv

theorem scan_body_duplicate_from_bounds
    (iter : core.array.iter.IntoIter U32 8#usize) (s : QueryScan)
    (candidate : Std.U32) (iter1 : core.array.iter.IntoIter U32 8#usize)
    (hnext : core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next iter =
      ok (some candidate, iter1))
    (hlen : s.accepted_len.val < 22) (hdraw : s.draws.val < 64)
    (hmember : candidate.val ∈ acceptedPrefix s) :
    ∃ drawNext,
      (s.draws + 1#usize : Result Std.Usize) = .ok drawNext ∧
      drawNext.val = s.draws.val + 1 ∧
      QueryScan.scan_loop.body iter s =
        .ok (.cont (iter1, { accepted := s.accepted, accepted_len := s.accepted_len, draws := drawNext })) ∧
      q22StateOfFresh { s with draws := drawNext } =
        ⟨acceptedPrefix s, s.draws.val + 1⟩ := by
  obtain ⟨drawNext, hdrawop, hdrawval⟩ := source_draw_increment_success s hdraw
  obtain ⟨sl, hsl, hslval⟩ := slice_read_prefix_success_dup s hlen
  have hnotfull := not_query_count_of_lt_dup s hlen
  have hnotcap := not_query_cap_of_lt_dup s hdraw
  have hbody := scan_body_duplicate_candidate iter s candidate iter1 drawNext sl
    hnext hnotfull hnotcap hdrawop hsl hslval hmember
  have hq22 := q22_state_duplicate_update s drawNext hdrawval
  exact ⟨drawNext, hdrawop, hdrawval, hbody, hq22⟩

#print axioms scan_body_duplicate_from_bounds
end AspisR1QueryScanUnrolled.r0_transcript

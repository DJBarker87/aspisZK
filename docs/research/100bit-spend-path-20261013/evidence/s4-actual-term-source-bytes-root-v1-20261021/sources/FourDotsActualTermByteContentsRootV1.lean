import FourDotsActualTermInputTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermByteContentsRootV1
open AspisR1FastDotsActualTermInputTraceRootV1
abbrev U8 := Std.U8

private theorem copied_bytes_contents
    (s : Slice U8) (copied : core.result.Result (Array U8 4#usize) core.array.TryFromSliceError)
    (bytes : Array U8 4#usize)
    (hcopy : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s = .ok copied)
    (hunwrap : core.result.Result.unwrap core.fmt.DebugTryFromSliceError copied = .ok bytes) :
    bytes.val=s.val := by
  unfold core.array.TryFromArrayCopySlice.try_from at hcopy
  split at hcopy
  · rename_i hlen
    have hc := Result.ok.inj hcopy
    subst copied
    have hb := Result.ok.inj hunwrap
    exact (congrArg Subtype.val hb).symm
  · have hc := Result.ok.inj hcopy
    subst copied
    cases hunwrap

private theorem actual_slice_contents
    (a : Array U8 608#usize) (start finish : Usize) (s : Slice U8)
    (hslice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a {start, «end» := finish} = .ok s) :
    s.val=a.val.slice start.val finish.val := by
  rw [Array.index_SliceIndexRangeUsizeSlice] at hslice
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hslice
  split at hslice
  · have heq := Result.ok.inj hslice
    exact (congrArg Subtype.val heq).symm
  · cases hslice

/-- Retained term bytes are exactly the source-buffer slice selected by the
same checked offset operations. The parser sees those same four bytes. -/
theorem actual_term_bytes_source_contents
    (a : Array U8 608#usize) (slot term : Usize) (bytes : Array U8 4#usize)
    (htrace : TermBytesTrace a slot term bytes) :
    ∃ (slotOffset termOffset start duplicateStart finish : Usize),
      (slot * 120#usize : Result Usize) = .ok slotOffset ∧
      (term * 4#usize : Result Usize) = .ok termOffset ∧
      (slotOffset+termOffset : Result Usize) = .ok start ∧
      (slotOffset+termOffset : Result Usize) = .ok duplicateStart ∧
      (duplicateStart+4#usize : Result Usize) = .ok finish ∧
      bytes.val=a.val.slice start.val finish.val := by
  rcases htrace with ⟨o0,o1,o2,o3,o4,s,c,h0,h1,h2,h3,h4,hs,hc,hb⟩
  refine ⟨o0,o1,o2,o3,o4,h0,h1,h2,h3,h4,?_⟩
  exact (copied_bytes_contents s c bytes hc hb).trans (actual_slice_contents a o2 o4 s hs)

/-- Successful retained scalar parsing returns the exact little-endian
word of the same source-selected bytes, not merely a bounded value. -/
theorem source_parser_success_word
    (bytes : Array U8 4#usize) (x : AspisR1DecodeKFullV10.aspis_core.field.M31)
    (h : AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes = .ok (some x)) :
    x=core.num.U32.from_le_bytes bytes := by
  unfold AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes at h
  simp only [lift,bind_tc_ok] at h
  change (if core.num.U32.from_le_bytes bytes >= AspisR1DecodeKFullV10.aspis_core.field.P
    then Result.ok none else Result.ok (some (core.num.U32.from_le_bytes bytes))) = Result.ok (some x) at h
  split at h
  · cases h
  · exact (Option.some.inj (Result.ok.inj h)).symm
#print axioms actual_term_bytes_source_contents
#print axioms source_parser_success_word
end AspisR1FastDotsActualTermByteContentsRootV1

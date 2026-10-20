import AspisR1FastDotsCurrent.FunsOpsFixedV6
import FourDotsFixedCallTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsFixedCallSuccessV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Prefix (q : Slice Std.U8) : Result (Array Std.U8 608#usize) := do
  let s ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) q { «end» := 608#usize }
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  core.result.Result.unwrap core.fmt.DebugTryFromSliceError r

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem fixed_success_calls_actual_helpers
    (ops : Ops) (q : Slice Std.U8) (g : Array Wide 29#usize)
    (out : Array Wide 4#usize)
    (h : AspisR1FastDotsCurrent.fast_dots.four_dots_fixed ops q g = .ok out) :
    ∃ q1 w0 w1 w2 w3,
      Prefix q = .ok q1 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 0#usize = .ok w0 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize = .ok w1 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize = .ok w2 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize = .ok w3 ∧
      out = Array.make 4#usize [w0, w1, w2, w3] := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots_fixed at h
  obtain ⟨s, hs, hrest⟩ := bind_success
    (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
      q { «end» := 608#usize })
    (fun s => do
      let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
      let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let w0 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 0#usize
      let w1 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize
      let w2 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out h
  obtain ⟨r, hr, hrest⟩ := bind_success
    (core.array.TryFromSharedArraySlice.try_from 608#usize s)
    (fun r => do
      let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let w0 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 0#usize
      let w1 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize
      let w2 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  obtain ⟨q1, hq1, hrest⟩ := bind_success
    (core.result.Result.unwrap core.fmt.DebugTryFromSliceError r)
    (fun q1 => do
      let w0 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 0#usize
      let w1 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize
      let w2 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  obtain ⟨w0, h0, hrest⟩ := bind_success
    (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 0#usize)
    (fun w0 => do
      let w1 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize
      let w2 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  obtain ⟨w1, h1, hrest⟩ := bind_success
    (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 1#usize)
    (fun w1 => do
      let w2 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  obtain ⟨w2, h2, hrest⟩ := bind_success
    (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 2#usize)
    (fun w2 => do
      let w3 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize
      ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  obtain ⟨w3, h3, hlast⟩ := bind_success
    (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q1 g 3#usize)
    (fun w3 => .ok (Array.make 4#usize [w0, w1, w2, w3])) out hrest
  have hprefix : Prefix q = .ok q1 := by
    unfold Prefix
    simp only [hs, bind_tc_ok, hr, hq1]
  have hout : out = Array.make 4#usize [w0, w1, w2, w3] :=
    (Result.ok.inj hlast).symm
  exact ⟨q1, w0, w1, w2, w3, hprefix, h0, h1, h2, h3, hout⟩

#print axioms fixed_success_calls_actual_helpers
end AspisR1FastDotsFixedCallSuccessV1

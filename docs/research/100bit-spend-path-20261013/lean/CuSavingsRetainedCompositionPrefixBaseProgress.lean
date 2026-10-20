import CuSavingsRetainedCompositionPrefixBaseStep

/-! Control-flow progress of the exact emitted base loop, independent of
arithmetic success. Explicit bind inversion avoids unbounded tactic search. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsRetainedCompositionPrefixBaseProgress
open Aeneas Aeneas.Std Result ControlFlow AspisR1RetainedDots
open CuSavingsLoopRelation OccupancyRangeTraversal

private theorem bind_ok {A B : Type} (p : Result A) (k : A → Result B) (y : B)
    (h : (p >>= k) = .ok y) : ∃ x, p = .ok x ∧ k x = .ok y := by
  cases hp : p with
  | fail e => simp only [hp,bind_tc_fail] at h;cases h
  | div => simp only [hp,bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,by simpa only [hp,bind_tc_ok] using h⟩

variable [Shared]
local notation "baseBody" =>
  new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body

theorem body_progress (bytes : Slice U8)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (sums : Array U64 8#usize) (hend : iter.end.val ≤ 26) :
    All (baseBody bytes gamma slot iter sums)
      (fun flow => match flow with
        | .done _ => True
        | .cont (next,_) => next.end.val ≤ 26 ∧
            next.end.val-next.start.val < iter.end.val-iter.start.val) := by
  by_cases halt : iter.start.val ≥ iter.end.val
  · have hn := next_done iter halt
    intro flow hf
    have hb : baseBody bytes gamma slot iter sums = .ok (.done sums) := by
      simp only [new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,
        hn,bind_tc_ok]
      rfl
    rw [hb] at hf
    cases hf
    trivial
  · obtain ⟨next,hn,hinc,hend1,_⟩ := next_step iter (by omega)
    intro flow hf
    simp only [new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,
      hn,bind_tc_ok] at hf
    change (do
      let i ← slot * 120#usize
      let i1 ← iter.start * 4#usize
      let i2 ← i + i1
      let i3 ← i + i1
      let i4 ← i3 + 4#usize
      let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start := i2,«end» := i4}
      let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s1
      let a1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let o1 ← field.M31.from_le_bytes a1
      let scalar ← core.option.Option.unwrap o1
      let we ← Array.index_usize gamma iter.start
      let coefficient ← field.wide_exact.WideExact.to_limbs we
      let sums1 ← new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0
        {start := 0#usize,«end» := field.wide_exact.WideExact.LIMB_COUNT} sums scalar coefficient
      .ok (ControlFlow.cont (β := Array U64 8#usize) (next,sums1))) = .ok flow at hf
    obtain ⟨i,hi,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i1,hi1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i2,hi2,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i3,hi3,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i4,hi4,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨s1,hs1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨r,hr,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨a1,ha1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨o1,ho1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨scalar,hscalar,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨we,hwe,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨coefficient,hcoefficient,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨sums1,hsums1,hf⟩ := bind_ok _ _ _ hf
    cases hf
    change next.end.val ≤ 26 ∧
      next.end.val-next.start.val < iter.end.val-iter.start.val
    rw [hend1,hinc]
    omega

#print axioms body_progress
end AspisR1.CuSavingsRetainedCompositionPrefixBaseProgress

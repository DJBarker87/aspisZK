import CuSavingsDotsBase
import CuSavingsQueryAccess

/-! Prefix invariance of the complete emitted two-term tail loop, including
its actual iterator bound, mutation handback and failure/divergence paths. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsDotsTail
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuDots
open CuSavingsPrefix CuSavingsDotsReads CuSavingsLoopRelation OccupancyRangeTraversal
open CuSavingsQueryAccess (bind_ok)
variable [Arithmetic]
local notation "tailBody" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body
local notation "tailLoop" =>
  old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1

theorem body_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (tail : fast_pairing.EbyKDot)
    (hs : slot.val < 4) (hend : iter.end.val ≤ 2) :
    tailBody (prefixArray bytes h).to_slice gamma slot iter tail =
      tailBody bytes gamma slot iter tail := by
  by_cases halt : iter.start.val ≥ iter.end.val
  · have hn := next_done iter halt
    simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
      hn,bind_tc_ok]
    rfl
  · obtain ⟨next,hn,hinc,hend1,_⟩ := next_step iter (by omega)
    simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
      hn,bind_tc_ok]
    exact tail_cont bytes h slot iter.start hs (by omega) (Array.index_usize gamma) _

theorem body_progress (bytes : Slice U8)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (tail : fast_pairing.EbyKDot) (hend : iter.end.val ≤ 2) :
    All (tailBody bytes gamma slot iter tail)
      (fun flow => match flow with
        | .done _ => True
        | .cont (next,_) => next.end.val ≤ 2 ∧
            next.end.val-next.start.val < iter.end.val-iter.start.val) := by
  by_cases halt : iter.start.val ≥ iter.end.val
  · have hn := next_done iter halt
    intro flow hf
    have hb : tailBody bytes gamma slot iter tail = .ok (.done tail) := by
      simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
        hn,bind_tc_ok]
      rfl
    rw [hb] at hf
    cases hf
    trivial
  · obtain ⟨next,hn,hinc,hend1,_⟩ := next_step iter (by omega)
    intro flow hf
    simp only [old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
      hn,bind_tc_ok] at hf
    change (do
      let i ← slot * 32#usize
      let i1 ← 480#usize + i
      let i2 ← iter.start * 16#usize
      let offset ← i1 + i2
      let i3 ← iter.start + 26#usize
      let we ← Array.index_usize gamma i3
      let i4 ← offset + 16#usize
      let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start := offset,«end» := i4}
      let o1 ← field.QM31.from_le_bytes s
      let q ← core.option.Option.unwrap o1
      let (r,tail1) ← fast_pairing.EbyKDot.push tail we q
      core.result.Result.unwrap core.fmt.DebugUnit r
      .ok (ControlFlow.cont (β := fast_pairing.EbyKDot) (next,tail1))) = .ok flow at hf
    obtain ⟨i,hi,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i1,hi1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i2,hi2,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨offset,hoff,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i3,hi3,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨we,hwe,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨i4,hi4,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨s,hs,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨o1,ho1,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨q,hq,hf⟩ := bind_ok _ _ _ hf
    obtain ⟨result,hresult,hf⟩ := bind_ok _ _ _ hf
    rcases result with ⟨r,tail1⟩
    change (do core.result.Result.unwrap core.fmt.DebugUnit r
               .ok (ControlFlow.cont (β := fast_pairing.EbyKDot) (next,tail1))) = .ok flow at hf
    obtain ⟨unit,hunit,hf⟩ := bind_ok _ _ _ hf
    cases hf
    change next.end.val ≤ 2 ∧
      next.end.val-next.start.val < iter.end.val-iter.start.val
    rw [hend1,hinc]
    omega

theorem source_eq (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (gamma : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (iter : Range) (tail : fast_pairing.EbyKDot)
    (hs : slot.val < 4) (hend : iter.end.val ≤ 2) :
    tailLoop iter (prefixArray bytes h).to_slice gamma slot tail =
      tailLoop iter bytes gamma slot tail := by
  unfold old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
  refine loop_eq
    (fun (it,acc) => tailBody (prefixArray bytes h).to_slice gamma slot it acc)
    (fun (it,acc) => tailBody bytes gamma slot it acc)
    (fun state => state.1.end.val ≤ 2)
    (fun state => state.1.end.val-state.1.start.val)
    ?_ ?_ (iter,tail) hend
  · intro state hi
    rcases state with ⟨it,acc⟩
    exact body_eq bytes h gamma slot it acc hs hi
  · intro state next hi hc
    rcases state with ⟨it,acc⟩
    rcases next with ⟨it1,acc1⟩
    exact body_progress bytes gamma slot it acc hi (.cont (it1,acc1)) hc

#print axioms body_eq
#print axioms body_progress
#print axioms source_eq
end AspisR1.CuSavingsDotsTail

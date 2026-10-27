import FJh_M31DotOuterSource
import FJh_M31DotChunkIterator
import FJh_M31DotChunkModel
import FJh_M31DotReduceLoop

/-! One checked outer chunk, preserving the actual recursive continuation.
Only the concrete checked start+4 and min operations are supplied by callers. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotOuterStep
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (Exact)
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalLaneReassembly (rawDecode)
open AspisR1.RawPoseidonRowField (decodeWords)
open AspisR1.FJh_M31DotReads
open AspisR1.FJh_M31DotOuterSource (Iter)
open AspisV8R17.RawReducer (P)

theorem source_advance (iter : Iter) (weights : Slice field.QM31) (values : Slice U32)
    (sums : Raw4) (plus last : Usize) (fuel n : Nat)
    (hstep : iter.step_by.val = 4) (hactive : iter.iter.start.val < iter.iter.end.val)
    (hplus : UScalar.add iter.iter.start 4#usize = .ok plus)
    (hmin : core.cmp.min core.cmp.OrdUsize plus (Slice.len weights) = .ok last)
    (hwEnd : last.val ≤ weights.val.length) (hvEnd : last.val ≤ values.val.length)
    (hspan : iter.iter.start.val+fuel=last.val) (hfuel : fuel ≤ 4)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values)
    (hn : n ≤ 15) (hs : RawBound sums (n*P)) :
    ∃ (next : Iter) (sums1 : Raw4),
      field.qm31_m31_dot_loop1 iter weights values sums =
        field.qm31_m31_dot_loop1 next weights values sums1 ∧
      next.iter.start.val = min (iter.iter.start.val+4) iter.iter.end.val ∧
      next.iter.end = iter.iter.end ∧ next.step_by.val = 4 ∧
      RawBound sums1 ((n+1)*P) ∧
      rawDecode sums1 = rawDecode sums + decodeWords (remaining weights values iter.iter.start.val fuel) := by
  obtain ⟨next,hnext,hstart,hend,hstep1⟩ :=
    AspisR1.FJh_M31DotChunkIterator.next_step iter hstep hactive
  obtain ⟨raw,hchunk,_,hraw⟩ := AspisR1.FJh_M31DotChunkModel.source_success
    weights values { start := iter.iter.start, «end» := last } fuel
      hwEnd hvEnd hspan hfuel hw hv
  obtain ⟨sums1,hreduce,hbound,hmodel⟩ :=
    AspisR1.FJh_M31DotReduceLoop.source_success sums raw n hn hs
  refine ⟨next,sums1,?_,hstart,hend,hstep1,hbound,?_⟩
  · rw [AspisR1.FJh_M31DotOuterSource.source_loop_eq,hnext]
    change (do
      let plus ← UScalar.add iter.iter.start 4#usize
      let last ← core.cmp.min core.cmp.OrdUsize plus (Slice.len weights)
      let raw ← field.qm31_m31_dot_loop1_loop0
        { start := iter.iter.start, «end» := last } weights values
        FJh_InternalAccumulateState.zero
      let sums1 ← field.qm31_m31_dot_loop1_loop1
        { start := 0#usize, «end» := 4#usize } sums raw
      field.qm31_m31_dot_loop1 next weights values sums1) =
      field.qm31_m31_dot_loop1 next weights values sums1
    simp only [hplus,hmin,hchunk,hreduce,bind_tc_ok]
  · have hdecode : rawDecode raw = decodeWords (remaining weights values iter.iter.start.val fuel) :=
      congrArg decodeWords (funext hraw)
    exact hmodel.trans (congrArg (rawDecode sums + ·) hdecode)

#print axioms source_advance
end AspisR1.FJh_M31DotOuterStep

import RPu_FJh_M31DotOuterStep
import RPu_FJh_M31DotRemainingAlgebra

/-! The actual seven-input internal-pair dot executes exactly two bounded
chunks. Source recursion is rewritten twice; coordinate arithmetic remains
symbolic throughout. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotSevenOuter
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalLaneReassembly (rawDecode)
open AspisR1.FJh_InternalAccumulateState (zero zero_value)
open AspisR1.FJh_Base (cell)
open AspisR1.RawPoseidonRowField (decodeWords decodeWords_add)
open AspisR1.FJh_M31DotReads
open AspisR1.FJh_M31DotChunkIterator (initial)
open AspisV8R17.RawReducer (P)

theorem len_seven {T : Type} (s : Slice T) (hs : s.val.length = 7) : Slice.len s = 7#usize := by
  apply UScalar.eq_of_val_eq
  change s.val.length = 7
  exact hs

theorem source_success (weights : Slice field.QM31) (values : Slice U32)
    (hwlen : weights.val.length = 7) (hvlen : values.val.length = 7)
    (hw : CanonicalWeights weights) (hv : CanonicalValues values) :
    ∃ out : Raw4,
      field.qm31_m31_dot_loop1 (initial (Slice.len weights)) weights values zero = .ok out ∧
      RawBound out (3*P) ∧ rawDecode out = decodeWords (remaining weights values 0 7) := by
  have hwlen' := len_seven weights hwlen
  have hz : RawBound zero (1*P) := by
    intro j
    rw [zero_value]
    norm_num [P]
  let iter0 := initial (Slice.len weights)
  have hstart0 : iter0.iter.start.val = 0 := rfl
  have hend0 : iter0.iter.end.val = 7 := by change (Slice.len weights).val = 7; rw [hwlen']; rfl
  have hiter0 : iter0.iter.start = 0#usize := UScalar.eq_of_val_eq hstart0
  have hsize4 : 8 < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all
  have hsize4small : 4 < 2 ^ System.Platform.numBits := by omega
  have hplus0 : UScalar.add iter0.iter.start 4#usize = .ok 4#usize := by
    rw [hiter0]
    simp [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, hsize4, hsize4small]
  have hmin0 : core.cmp.min core.cmp.OrdUsize 4#usize (Slice.len weights) = .ok 4#usize := by
    rw [hwlen']
    simp [core.cmp.min, core.cmp.OrdUsize, core.cmp.impls.OrdUsize.min]
  obtain ⟨iter1,sums1,hrun0,hstart1,hend1,hstep1,hbound1,hmodel1⟩ :=
    AspisR1.FJh_M31DotOuterStep.source_advance iter0 weights values zero 4#usize 4#usize 4 1
      (by rfl) (by rw [hstart0,hend0]; decide) hplus0 hmin0
      (by rw [hwlen]; decide) (by rw [hvlen]; decide) (by rw [hstart0]; decide)
      (by decide) hw hv (by decide) hz
  have hstart1' : iter1.iter.start.val = 4 := by rw [hstart1,hstart0,hend0]; decide
  have hend1' : iter1.iter.end.val = 7 := by rw [hend1]; exact hend0
  have hstart1eq : iter1.iter.start = 4#usize := UScalar.eq_of_val_eq hstart1'
  have hplus1 : UScalar.add iter1.iter.start 4#usize = .ok 8#usize := by
    rw [hstart1eq]
    simp [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, hsize4, hsize4small]
  have hmin1 : core.cmp.min core.cmp.OrdUsize 8#usize (Slice.len weights) = .ok 7#usize := by
    rw [hwlen']
    simp [core.cmp.min, core.cmp.OrdUsize, core.cmp.impls.OrdUsize.min]
  obtain ⟨iter2,sums2,hrun1,hstart2,hend2,hstep2,hbound2,hmodel2⟩ :=
    AspisR1.FJh_M31DotOuterStep.source_advance iter1 weights values sums1 8#usize 7#usize 3 2
      hstep1 (by rw [hstart1',hend1']; decide) hplus1 hmin1
      (by rw [hwlen]; decide) (by rw [hvlen]; decide) (by rw [hstart1']; decide)
      (by decide) hw hv (by decide) hbound1
  have hstop : iter2.iter.start.val ≥ iter2.iter.end.val := by
    rw [hstart2,hend2,hstart1',hend1']
    decide
  have hnext2 := AspisR1.FJh_M31DotChunkIterator.next_done iter2 hstop
  have hrun2 : field.qm31_m31_dot_loop1 iter2 weights values sums2 = .ok sums2 := by
    rw [AspisR1.FJh_M31DotOuterSource.source_loop_eq,hnext2]
    rfl
  have hzero : rawDecode zero = 0 := by
    ext <;> simp [rawDecode,decodeWords,zero_value]
  have hsplit : decodeWords (remaining weights values 0 7) =
      decodeWords (remaining weights values 0 4) + decodeWords (remaining weights values 4 3) := by
    have hfun : remaining weights values 0 7 = (fun j : Fin 4 =>
        remaining weights values 0 4 j + remaining weights values 4 3 j) := by
      funext j
      exact AspisR1.FJh_M31DotRemainingAlgebra.remaining_add weights values 0 4 3 j
    exact (congrArg decodeWords hfun).trans (decodeWords_add _ _)
  refine ⟨sums2,hrun0.trans (hrun1.trans hrun2),hbound2,?_⟩
  rw [hmodel2,hmodel1,hstart0,hstart1',hzero,zero_add]
  exact hsplit.symm

#print axioms len_seven
#print axioms source_success
end AspisR1.FJh_M31DotSevenOuter

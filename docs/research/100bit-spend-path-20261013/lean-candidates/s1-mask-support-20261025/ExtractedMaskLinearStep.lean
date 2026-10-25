import AspisR1SelectedMaskProbe.Funs
import ExtractedMaskReverseRange
import ExtractedMaskHornerStep
import ExtractedMaskQM31Exact

/-! Draft only: exact done/one-step facts for the generated reverse loop 0 in
`selected_mask_linears`.  No recurrence is unfolded and no semantic relation
is asserted. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskLinearStep

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def decode (x : QM) : AspisV8R15.ExactTowerBase.QM31Exact :=
  AspisR1.ExtractedMaskQM31Exact.decode x

def pointAt (point : Array QM 10#usize) (i : Usize)
    (hi : i.val < (10#usize : Usize).val) : QM :=
  point.val[i.val]'(by simpa [point.property] using hi)

/-- Existing actual-Aeneas checked array read, specialized only to the
    generated point array's length. -/
theorem array_index_usize_ok (point : Array QM 10#usize) (i : Usize)
    (hi : i.val < (10#usize : Usize).val) :
    Array.index_usize point i = .ok (pointAt point i hi) := by
  exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok point i hi

/-- When the reverse iterator is finished, the extracted body returns the
    unchanged `(suffix, weighted)` pair. -/
theorem body0_done (point : Array QM 10#usize) (iter : ReverseRange)
    (suffix weighted : QM) (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    state_only_hiding.selected_mask_linears_loop.body point iter suffix weighted =
      .ok (.done (suffix, weighted)) := by
  simp only [state_only_hiding.selected_mask_linears_loop.body,
    reverse_next_done iter hstop, bind_tc_ok]

/-- The zero-index step updates the suffix but deliberately leaves `weighted`
    unchanged. This is the source's `if variable1 != 0` skip branch. -/
theorem body0_step_zero
    (point : Array QM 10#usize) (iter : ReverseRange)
    (suffix weighted q : QM)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
      (10#usize : Usize).val)
    (hzero : Usize.wrapping_sub iter.iter.end 1#usize = 0#usize)
    (hget : Array.index_usize point
      (Usize.wrapping_sub iter.iter.end 1#usize) = .ok q)
    (hsuffix : CanonicalQM suffix) (hweighted : CanonicalQM weighted)
    (hq : CanonicalQM q) :
    ∃ suffix1 : QM,
      state_only_hiding.selected_mask_linears_loop.body point iter suffix weighted =
        .ok (.cont
          (⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩,
            suffix1, weighted)) ∧
      CanonicalQM suffix1 ∧
      decode suffix1 = decode suffix + decode q := by
  obtain ⟨suffix1, hadd, hcanon, hvalue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact suffix q hsuffix hq
  refine ⟨suffix1, ?_, hcanon, hvalue⟩
  have hget0 : Array.index_usize point 0#usize = .ok q := by
    rw [← hzero]
    exact hget
  simp only [state_only_hiding.selected_mask_linears_loop.body,
    reverse_next_step iter hstep, bind_tc_ok, hzero, hget0, hadd]
  have hfalse : (0#usize != 0#usize) = false := by decide
  rw [hfalse]
  rfl

/-- A nonzero reverse index updates both accumulators, in source return order
    `(iter1, suffix1, weighted1)`. -/
theorem body0_step_nonzero
    (point : Array QM 10#usize) (iter : ReverseRange)
    (suffix weighted q : QM)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
      (10#usize : Usize).val)
    (hnzero : Usize.wrapping_sub iter.iter.end 1#usize ≠ 0#usize)
    (hget : Array.index_usize point
      (Usize.wrapping_sub iter.iter.end 1#usize) = .ok q)
    (hsuffix : CanonicalQM suffix) (hweighted : CanonicalQM weighted)
    (hq : CanonicalQM q) :
    ∃ suffix1 weighted1 : QM,
      state_only_hiding.selected_mask_linears_loop.body point iter suffix weighted =
        .ok (.cont
          (⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩,
            suffix1, weighted1)) ∧
      CanonicalQM suffix1 ∧ CanonicalQM weighted1 ∧
      decode suffix1 = decode suffix + decode q ∧
      decode weighted1 = decode weighted + decode suffix1 := by
  obtain ⟨suffix1, hadd, hcanon, hvalue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact suffix q hsuffix hq
  obtain ⟨weighted1, haddw, hcanonw, hvaluew⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact weighted suffix1
      hweighted hcanon
  refine ⟨suffix1, weighted1, ?_, hcanon, hcanonw, hvalue, hvaluew⟩
  simp only [state_only_hiding.selected_mask_linears_loop.body,
    reverse_next_step iter hstep, bind_tc_ok, hget, hadd, haddw]
  simp [hnzero]

#print axioms array_index_usize_ok
#print axioms body0_done
#print axioms body0_step_zero
#print axioms body0_step_nonzero

end AspisR1.ExtractedMaskLinearStep

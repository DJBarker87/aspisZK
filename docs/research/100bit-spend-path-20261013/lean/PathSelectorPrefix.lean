import SumHighBoxedModel
import SelectorMarginalModel
import ExtractedMaskQM31Exact

/-! Actual path-selector prefix: bounded high-range summation, four checked
low-array reads, three additions and multiplication, on the same boxed point. -/
set_option autoImplicit false
namespace AspisR1.PathSelectorPrefix
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.ExtractedMaskQM31Exact

abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lowAt (selectors : Selectors) :=
  AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low

private theorem index_ok {α : Type} {N : Usize}
    (a : Array α N) (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem readLow_success (selectors : Selectors) (index : Usize)
    (hindex : index.val < 16) (hlow : CanonicalArray selectors.low) :
    ∃ q, Array.index_usize selectors.low index = .ok q ∧ Canonical q ∧
      decode q = lowAt selectors index.val := by
  let q := selectors.low.val[index.val]'(by simpa [selectors.low.property] using hindex)
  refine ⟨q, ?_, ?_, ?_⟩
  · exact index_ok selectors.low index (by simpa using hindex)
  · exact hlow ⟨index.val, by simpa using hindex⟩
  · have hiBound : index.val < (16#usize).val := by scalar_tac
    simp only [lowAt, AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt, dif_pos hiBound,
      AspisR1.SelectorExpansionCorrectness.decode]
    rfl

def runLow (selectors : Selectors) : Result QM := do
  let q1 ← Array.index_usize selectors.low 1#usize
  let q2 ← Array.index_usize selectors.low 5#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.low 9#usize
  let q5 ← field.QM31.add q3 q4
  let q6 ← Array.index_usize selectors.low 13#usize
  field.QM31.add q5 q6

theorem low_success (selectors : Selectors) (hlow : CanonicalArray selectors.low) :
    ∃ out, runLow selectors = .ok out ∧ Canonical out ∧
      decode out = ((lowAt selectors 1 + lowAt selectors 5) + lowAt selectors 9) + lowAt selectors 13 := by
  obtain ⟨q1, hr1, hc1, hv1⟩ := readLow_success selectors 1#usize (by scalar_tac) hlow
  obtain ⟨q2, hr2, hc2, hv2⟩ := readLow_success selectors 5#usize (by scalar_tac) hlow
  obtain ⟨q3, hr3, hc3, hv3⟩ := current_qm_add_exact q1 q2 hc1 hc2
  obtain ⟨q4, hr4, hc4, hv4⟩ := readLow_success selectors 9#usize (by scalar_tac) hlow
  obtain ⟨q5, hr5, hc5, hv5⟩ := current_qm_add_exact q3 q4 hc3 hc4
  obtain ⟨q6, hr6, hc6, hv6⟩ := readLow_success selectors 13#usize (by scalar_tac) hlow
  obtain ⟨out, hr7, hc7, hv7⟩ := current_qm_add_exact q5 q6 hc5 hc6
  have h1 : (1#usize).val = 1 := by scalar_tac
  have h5 : (5#usize).val = 5 := by scalar_tac
  have h9 : (9#usize).val = 9 := by scalar_tac
  have h13 : (13#usize).val = 13 := by scalar_tac
  simp only [h1, h5, h9, h13] at hv1 hv2 hv4 hv6
  refine ⟨out, ?_, hc7, ?_⟩
  · simp only [runLow, hr1, bind_tc_ok, hr2, hr3, hr4, hr5, hr6, hr7]
  · rw [hv7, hv5, hv3, hv1, hv2, hv4, hv6]

def lowModel {K : Type} [Field K] (sel : R0P.Sel K) : K :=
  ((R0P.g2Low sel 1 + R0P.g2Low sel 5) + R0P.g2Low sel 9) + R0P.g2Low sel 13

theorem boxed_low_success
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ out, runLow selectors = .ok out ∧ Canonical out ∧
      decode out = lowModel (pointSelector point) := by
  obtain ⟨_hhigh, hlow, _hhighModel, hlowModel⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  obtain ⟨out, hrun, hcanonical, hmodel⟩ := low_success selectors hlow
  refine ⟨out, hrun, hcanonical, ?_⟩
  change decode out = ((lowAt selectors 1 + lowAt selectors 5) +
    lowAt selectors 9) + lowAt selectors 13 at hmodel
  have h1 := hlowModel (1 : Fin 16)
  have h5 := hlowModel (5 : Fin 16)
  have h9 := hlowModel (9 : Fin 16)
  have h13 := hlowModel (13 : Fin 16)
  change lowAt selectors 1 = _ at h1
  change lowAt selectors 5 = _ at h5
  change lowAt selectors 9 = _ at h9
  change lowAt selectors 13 = _ at h13
  unfold lowModel
  exact hmodel.trans (by rw [h1, h5, h9, h13])

def run (selectors : Selectors) : Result QM := do
  let high ← AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high selectors
    (AspisR1.SumHighSingleRange.singleton AspisR1.SumHighBoxedModel.pathRange)
  let low ← runLow selectors
  field.QM31.mul high low

theorem pathSelector_model {K : Type} [Field K] (sel : R0P.Sel K) :
    R0P.g2SumHigh sel 57 6 (by omega) * lowModel sel = R0P.pathSelector sel := by
  unfold R0P.pathSelector lowModel
  rfl

attribute [local irreducible] R0P.g2Low R0P.g2High R0P.g2SumHigh

theorem boxed_path_selector
    (point : Array QM 10#usize) (selectors : Selectors)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors) :
    ∃ out, run selectors = .ok out ∧ Canonical out ∧
      decode out = R0P.pathSelector (pointSelector point) := by
  obtain ⟨high, hhigh, hchigh, hvhigh⟩ :=
    AspisR1.SumHighBoxedModel.boxed_path_sum point selectors hpoint hbox
  obtain ⟨low, hlow, hclow, hvlow⟩ := boxed_low_success point selectors hpoint hbox
  obtain ⟨out, hmul, hcanonical, hvalue⟩ := current_qm_mul_exact high low hchigh hclow
  refine ⟨out, ?_, hcanonical, ?_⟩
  · simp only [run, hhigh, bind_tc_ok, hlow, hmul]
  · rw [hvalue, hvhigh, hvlow]
    exact pathSelector_model (pointSelector point)

#print axioms readLow_success
#print axioms low_success
#print axioms boxed_low_success
#print axioms pathSelector_model
#print axioms boxed_path_selector
end
end AspisR1.PathSelectorPrefix

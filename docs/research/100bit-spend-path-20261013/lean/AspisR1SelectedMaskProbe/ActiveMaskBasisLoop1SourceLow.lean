import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev LowIndex := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.LowIndex

private theorem bind_result_id {α : Type} (r : Result α) :
    (do let x ← r; Result.ok x) = r := by
  cases r <;> rfl

def idx (n : Usize) (h : n.val < 16) : LowIndex := ⟨n, h⟩

def lowIndices (coordinate : Usize) : List LowIndex :=
  match coordinate.val with
  | 0 => [idx 11#usize (by decide), idx 12#usize (by decide)]
  | 1 => [idx 0#usize (by decide), idx 11#usize (by decide), idx 12#usize (by decide)]
  | 2 => [idx 0#usize (by decide), idx 12#usize (by decide)]
  | 3 => [idx 11#usize (by decide)]
  | 4 => [idx 0#usize (by decide), idx 11#usize (by decide)]
  | 5 => [idx 1#usize (by decide), idx 2#usize (by decide), idx 5#usize (by decide),
      idx 6#usize (by decide), idx 9#usize (by decide), idx 10#usize (by decide),
      idx 13#usize (by decide), idx 14#usize (by decide)]
  | 6 => [idx 0#usize (by decide), idx 2#usize (by decide), idx 4#usize (by decide),
      idx 6#usize (by decide), idx 7#usize (by decide), idx 9#usize (by decide),
      idx 10#usize (by decide)]
  | _ => []

def sourceLowSum (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (coordinate : Usize) : Result QM :=
  match coordinate.val with
  | 0 => do
      let q ← Array.index_usize self.low 11#usize
      let q1 ← Array.index_usize self.low 12#usize
      field.QM31.add q q1
  | 1 => do
      let q ← Array.index_usize self.low 0#usize
      let q1 ← Array.index_usize self.low 11#usize
      let q2 ← field.QM31.add q q1
      let q3 ← Array.index_usize self.low 12#usize
      field.QM31.add q2 q3
  | 2 => do
      let q ← Array.index_usize self.low 0#usize
      let q1 ← Array.index_usize self.low 12#usize
      field.QM31.add q q1
  | 3 => Array.index_usize self.low 11#usize
  | 4 => do
      let q ← Array.index_usize self.low 0#usize
      let q1 ← Array.index_usize self.low 11#usize
      field.QM31.add q q1
  | 5 => do
      let q ← Array.index_usize self.low 1#usize
      let q1 ← Array.index_usize self.low 2#usize
      let q2 ← field.QM31.add q q1
      let q3 ← Array.index_usize self.low 5#usize
      let q4 ← field.QM31.add q2 q3
      let q5 ← Array.index_usize self.low 6#usize
      let q6 ← field.QM31.add q4 q5
      let q7 ← Array.index_usize self.low 9#usize
      let q8 ← field.QM31.add q6 q7
      let q9 ← Array.index_usize self.low 10#usize
      let q10 ← field.QM31.add q8 q9
      let q11 ← Array.index_usize self.low 13#usize
      let q12 ← field.QM31.add q10 q11
      let q13 ← Array.index_usize self.low 14#usize
      field.QM31.add q12 q13
  | 6 => do
      let q ← Array.index_usize self.low 0#usize
      let q1 ← Array.index_usize self.low 2#usize
      let q2 ← field.QM31.add q q1
      let q3 ← Array.index_usize self.low 4#usize
      let q4 ← field.QM31.add q2 q3
      let q5 ← Array.index_usize self.low 6#usize
      let q6 ← field.QM31.add q4 q5
      let q7 ← Array.index_usize self.low 7#usize
      let q8 ← field.QM31.add q6 q7
      let q9 ← Array.index_usize self.low 9#usize
      let q10 ← field.QM31.add q8 q9
      let q11 ← Array.index_usize self.low 10#usize
      field.QM31.add q10 q11
  | _ => .fail Error.panic

def decodedLow (self : pool_v1.pair_forest_copy_terminal.Selectors) : Fin 16 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (self.low.val[i.val]'(by simpa [self.low.property] using i.isLt))

theorem sourceLowSum_eq_lowSum
    (self : pool_v1.pair_forest_copy_terminal.Selectors) (coordinate : Usize) :
    sourceLowSum self coordinate =
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSum self
        (lowIndices coordinate) := by
  by_cases hcoord : coordinate.val < 7
  · unfold sourceLowSum
    interval_cases hval : coordinate.val <;>
      simp [hval, lowIndices, idx,
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSum,
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSumFrom,
        bind_tc_ok, bind_result_id]
  · have hge : 7 ≤ coordinate.val := by omega
    have h0 : coordinate.val ≠ 0 := by omega
    have h1 : coordinate.val ≠ 1 := by omega
    have h2 : coordinate.val ≠ 2 := by omega
    have h3 : coordinate.val ≠ 3 := by omega
    have h4 : coordinate.val ≠ 4 := by omega
    have h5 : coordinate.val ≠ 5 := by omega
    have h6 : coordinate.val ≠ 6 := by omega
    unfold sourceLowSum
    simp [lowIndices, h0, h1, h2, h3, h4, h5, h6,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSum,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSumFrom,
      bind_tc_ok, bind_result_id]

theorem lowItems_eq_model
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (coordinate : Usize) (hcoordinate : coordinate.val < 7) :
    (AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowItems self
      (lowIndices coordinate)).sum =
        R0P.activeMaskLowSum (decodedLow self)
          (R0P.activeMaskBasisMasks ⟨coordinate.val, hcoordinate⟩) := by
  unfold lowIndices
  interval_cases hval : coordinate.val <;>
    simp [hval, idx, decodedLow,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowItems,
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowCell,
      R0P.activeMaskBasisMasks, R0P.activeMaskLowSum, hval, add_assoc]

theorem sourceLowSum_success
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (coordinate : Usize) (hcoordinate : coordinate.val < 7)
    (hlow : AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.CanonicalArray self.low) :
    ∃ out : QM, sourceLowSum self coordinate = .ok out ∧
      AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        R0P.activeMaskLowSum (decodedLow self)
          (R0P.activeMaskBasisMasks ⟨coordinate.val, hcoordinate⟩) := by
  have hnonempty : lowIndices coordinate ≠ [] := by
    unfold lowIndices
    interval_cases hval : coordinate.val <;> simp [hval, idx]
  obtain ⟨out, hrun, hcan, hdecode⟩ :=
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum.lowSum_exact
      self (lowIndices coordinate) hnonempty hlow
  refine ⟨out, ?_, hcan, ?_⟩
  · rw [sourceLowSum_eq_lowSum]
    exact hrun
  · rw [hdecode, lowItems_eq_model self coordinate hcoordinate]

#print axioms sourceLowSum_success
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow

import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow
import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1LowSum
import ExtractedMaskQM31Exact
import ArrayUpdateCanonicalExact

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a
abbrev LowSum := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow.sourceLowSum
abbrev LowSumMeaning (low : Fin 16 → ExactQM) (mask : Nat) :=
  R0P.activeMaskLowSum low mask
abbrev LowSumModel := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow.decodedLow

private theorem index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

def rebasedBody (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (sum : QM) (coordinate : Usize) := do
  let s ← lift (Array.to_slice
    pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS)
  let i := Slice.len s
  if coordinate < i then
    let low_sum ← LowSum self coordinate
    let q ← Array.index_usize highSums coordinate
    let q1 ← field.QM31.mul q low_sum
    let sum1 ← field.QM31.add sum q1
    let coordinate1 ← coordinate + 1#usize
    ok (cont (sum1, coordinate1))
  else ok (done sum)

theorem loop1_body_step
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (sum : QM) (coordinate : Usize)
    (hcoordinate : coordinate.val < 7)
    (hhighSums : CanonicalArray highSums) (hlow : CanonicalArray self.low)
    (hsum : CanonicalQM sum) :
    ∃ lowSum : QM, ∃ sum1 : QM, ∃ coordinate1 : Usize,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
        self highSums sum coordinate = .ok (.cont (sum1, coordinate1)) ∧
      LowSum self coordinate = .ok lowSum ∧
      UScalar.add coordinate 1#usize = .ok coordinate1 ∧
      CanonicalQM lowSum ∧ CanonicalQM sum1 ∧
      AspisR1.ExtractedMaskQM31Exact.decode sum1 =
        AspisR1.ExtractedMaskQM31Exact.decode sum +
          AspisR1.ExtractedMaskQM31Exact.decode
            (highSums.val[coordinate.val]'(by
              simpa [highSums.property] using hcoordinate)) *
            LowSumMeaning (LowSumModel self)
              (R0P.activeMaskBasisMasks ⟨coordinate.val, hcoordinate⟩) := by
  obtain ⟨lowValue, hlowRun, hlowCanonical, hlowValue⟩ :=
    AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1SourceLow.sourceLowSum_success
      self coordinate hcoordinate hlow
  let highCell := highSums.val[coordinate.val]'(by
    simpa [highSums.property] using hcoordinate)
  have hhighRead : Array.index_usize highSums coordinate = .ok highCell := by
    exact index_usize_ok highSums coordinate hcoordinate
  have hhighCanonical : CanonicalQM highCell := by
    exact hhighSums ⟨coordinate.val, by
      simpa [highSums.property] using hcoordinate⟩
  obtain ⟨product, hmul, hproductCanonical, hproductValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact highCell lowValue
      hhighCanonical hlowCanonical
  obtain ⟨sum1, hadd, hsum1Canonical, hsum1Value⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact sum product hsum hproductCanonical
  have hcoordinateBound : coordinate.val + (1#usize).val ≤ Usize.max := by scalar_tac
  have hincSpec : (coordinate + 1#usize : Result Usize) ⦃z => z.val = coordinate.val + (1#usize).val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hcoordinateBound
  obtain ⟨coordinate1, hinc, hcoordinate1⟩ := WP.spec_imp_exists hincSpec
  have hlen : Slice.len (Array.to_slice
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS) = 7#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len, Slice.length, Array.to_slice,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS]
  have hlt : coordinate < 7#usize := by
    apply (UScalar.lt_equiv coordinate 7#usize).2
    simpa using hcoordinate
  have hbodyEq : pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
      self highSums sum coordinate = rebasedBody self highSums sum coordinate := rfl
  have hbody : pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
      self highSums sum coordinate = .ok (.cont (sum1, coordinate1)) := by
    rw [hbodyEq]
    simp only [rebasedBody, lift, hlen, if_pos hlt, hlowRun, hhighRead, hmul, hadd,
      hinc, bind_tc_ok]
  refine ⟨lowValue, sum1, coordinate1, hbody, hlowRun, hinc,
    hlowCanonical, hsum1Canonical, ?_⟩
  rw [hsum1Value, hproductValue, hlowValue]

#print axioms loop1_body_step
end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step

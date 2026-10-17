import AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
namespace AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.ArrayUpdateCanonicalExact.CanonicalArray a
abbrev LowSumMeaning := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumMeaning
abbrev LowSumModel := AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.LowSumModel

def cell {n : Usize} (a : Array QM n) (j : Fin n.val) : QM :=
  a.val[j.val]'(by simpa [a.property] using j.isLt)

def term (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (i : Nat) : ExactQM :=
  if hi : i < 7 then
    AspisR1.ExtractedMaskQM31Exact.decode (cell highSums ⟨i, by simpa [highSums.property] using hi⟩) *
      LowSumMeaning (LowSumModel self) (R0P.activeMaskBasisMasks ⟨i, hi⟩)
  else 0

def prefixValue (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) : Nat → ExactQM
  | 0 => 0
  | n + 1 => prefixValue self highSums n + term self highSums n

theorem loop1_success_fuel_prefix
    (self : pool_v1.pair_forest_copy_terminal.Selectors)
    (highSums : Array QM 7#usize) (sum : QM) (coordinate : Usize) (fuel : Nat)
    (hspan : coordinate.val + fuel = 7)
    (hhigh : CanonicalArray highSums) (hlow : CanonicalArray self.low)
    (hsum : CanonicalQM sum)
    (hinv : AspisR1.ExtractedMaskQM31Exact.decode sum =
      prefixValue self highSums coordinate.val) :
    ∃ out : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1
        self highSums sum coordinate = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = prefixValue self highSums 7 := by
  induction fuel generalizing coordinate sum with
  | zero =>
      have hcoordinate : coordinate.val = 7 := by omega
      have hlen : Slice.len (Array.to_slice
          pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS) = 7#usize := by
        apply UScalar.eq_of_val_eq
        simp [Slice.len, Slice.length, Array.to_slice,
          pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS]
      have h7val : (7#usize).val = 7 := rfl
      have hnotVal : ¬ coordinate.val < 7 := by omega
      have hnot : ¬ coordinate < 7#usize := by
        intro hc
        have hlt := (UScalar.lt_equiv coordinate 7#usize).1 hc
        omega
      have hbody : pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
          self highSums sum coordinate = .ok (.done sum) := by
        simp [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body,
          lift, hlen, hnot, hnotVal, h7val]
      refine ⟨sum, ?_, hsum, ?_⟩
      · rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1, loop.eq_def]
        dsimp only
        rw [hbody]
      · simpa [hcoordinate, prefixValue] using hinv
  | succ fuel ih =>
      have hcoordinate : coordinate.val < 7 := by omega
      obtain ⟨_lowSum, sum1, coordinate1, hbody, _hlowRun, hinc,
          _hlowCanonical, hsum1Canonical, hsum1Value⟩ :=
        AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Step.loop1_body_step
          self highSums sum coordinate hcoordinate hhigh hlow hsum
      have hinc' : (coordinate + 1#usize : Result Usize) = .ok coordinate1 := by
        change UScalar.add coordinate 1#usize = .ok coordinate1
        exact hinc
      have haddSpec := UScalar.add_equiv coordinate (1#usize)
      rw [hinc'] at haddSpec
      simp only [Result.ok.injEq] at haddSpec
      have hcoordinate1 : coordinate1.val = coordinate.val + 1 := haddSpec.2.1
      have hspan1 : coordinate1.val + fuel = 7 := by omega
      have hprefix1 : prefixValue self highSums coordinate1.val =
          prefixValue self highSums coordinate.val + term self highSums coordinate.val := by
        rw [hcoordinate1]
        rfl
      have hinv1 : AspisR1.ExtractedMaskQM31Exact.decode sum1 =
          prefixValue self highSums coordinate1.val := by
        rw [hsum1Value, hinv, hprefix1]
        have hterm : term self highSums coordinate.val =
            AspisR1.ExtractedMaskQM31Exact.decode
                (cell highSums ⟨coordinate.val, by
                  simpa [highSums.property] using hcoordinate⟩) *
              LowSumMeaning (LowSumModel self)
                (R0P.activeMaskBasisMasks ⟨coordinate.val, hcoordinate⟩) := by
          simp [term, hcoordinate]
        rw [hterm]
        have hcell : cell highSums ⟨coordinate.val, by
            simpa [highSums.property] using hcoordinate⟩ =
            highSums.val[coordinate.val]'(by
              simpa [highSums.property] using hcoordinate) := rfl
        rw [← hcell]
      obtain ⟨out, hrun, houtCanonical, houtValue⟩ :=
        ih (coordinate := coordinate1) (sum := sum1) (hspan := hspan1)
          (hsum := hsum1Canonical) (hinv := hinv1)
      refine ⟨out, ?_, houtCanonical, houtValue⟩
      rw [pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1, loop.eq_def]
      dsimp only
      rw [hbody]
      exact hrun

end AspisR1SelectedMaskProbe.ActiveMaskBasisLoop1Fuel

import ExtractedMaskHornerStep

/-! Whole actual reverse mask loop, parameterized by the range length. The
recursive model is a symbolic Nat recurrence; no 26-step reduction is run. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskHornerLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskPreparedState
open AspisR1.ExtractedMaskPreparedMul
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskHornerStep

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Coefficients := Aeneas.Std.Array QM 27#usize
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

private def exactCoefficient (coefficients : Coefficients) (i : Nat) : ExactQM :=
  if hi : i < 27 then
    decode (coefficients.val[i]'(by simpa [coefficients.property] using hi))
  else 0

/-- Mathematical recurrence for processing coefficient indices downward.
For a range of length `n`, the next state uses coefficient `n-1`; the
recurrence remains symbolic for every `n`. -/
def hornerLoopModel (coefficients : Nat → ExactQM) (linear : ExactQM) :
    Nat → ExactQM → ExactQM
  | 0, acc => acc
  | n + 1, acc =>
      hornerLoopModel coefficients linear n
        (linear * acc + coefficients n)

theorem body_loop2_model (coefficients : Coefficients) (prepared : Prepared)
    (linear : QM) (iter : ReverseRange) (n : Nat) (shared : QM)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n)
    (hn : n ≤ 27) (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear)
    (hcoefficients : ∀ i : Fin 27,
      CanonicalQM (coefficients.val[i.val]'(by
        simpa [coefficients.property] using
          (show i.val < (27#usize : Usize).val by simpa))))
    (hshared : CanonicalQM shared) :
    ∃ out : QM,
      state_only_hiding.state_only_selected_mask_value_loop2
        iter coefficients prepared shared = .ok out ∧
      CanonicalQM out ∧
      decode out = hornerLoopModel (exactCoefficient coefficients)
        (decode linear) n (decode shared) := by
  induction n generalizing iter shared with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      refine ⟨shared, ?_, hshared, ?_⟩
      · rw [state_only_hiding.state_only_selected_mask_value_loop2,
          loop.eq_def]
        dsimp only
        simp only [body2_done coefficients prepared iter shared hstop,
          bind_tc_ok]
      · rfl
  | succ n ih =>
      have hstep : iter.iter.start.val < iter.iter.end.val := by omega
      have hend_pos : 1 ≤ iter.iter.end.val := by omega
      have hindexVal :
          (Usize.wrapping_sub iter.iter.end 1#usize).val = n := by
        rw [wrapping_sub_one_val _ hend_pos]
        omega
      have hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
          (27#usize : Usize).val := by
        rw [hindexVal]
        have h27 : (27#usize : Usize).val = 27 := by rfl
        omega
      let idx := Usize.wrapping_sub iter.iter.end 1#usize
      have hcoefficientCanon : CanonicalQM
          (coefficientAt coefficients idx hindex) := by
        have h := hcoefficients ⟨n, by
          have h27 : (27#usize : Usize).val = 27 := by rfl
          omega⟩
        simpa [coefficientAt, idx, hindexVal] using h
      obtain ⟨shared1, hbody, hshared1, hvalue⟩ :=
        body2_step coefficients prepared iter linear shared hstep hindex
          hlinear hshared hprepared hcoefficientCanon
      let iter1 : ReverseRange :=
        ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
      have hstart1 : iter1.iter.start.val = 0 := by
        simpa [iter1] using hstart
      have hend1 : iter1.iter.end.val = n := by
        dsimp [iter1]
        rw [wrapping_sub_one_val _ hend_pos]
        omega
      have hrec := ih iter1 shared1 hstart1 hend1 (by omega) hshared1
      obtain ⟨out, hrun, hout, hmodel⟩ := hrec
      refine ⟨out, ?_, hout, ?_⟩
      · rw [state_only_hiding.state_only_selected_mask_value_loop2,
          loop.eq_def]
        dsimp only
        simp only [hbody, bind_tc_ok]
        exact hrun
      · have hcoeffEq :
            decode (coefficientAt coefficients idx hindex) =
              exactCoefficient coefficients n := by
          have hnb : n < 27 := by omega
          simp [coefficientAt, exactCoefficient, idx, hindexVal, hnb]
        dsimp only [idx] at hcoeffEq
        rw [hornerLoopModel, hmodel, hvalue, hcoeffEq]

#print axioms body_loop2_model
end AspisR1.ExtractedMaskHornerLoop

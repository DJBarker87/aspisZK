import ExtractedMaskLinearStep

/-! Draft only: whole actual reverse accumulator loop, parameterized by the
range end. The model uses a Nat-indexed point accessor so the induction does
not construct `Fin 10` at an arbitrary recursive index. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskLinearLoop

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskLinearStep

abbrev QM := field.QM31
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev CanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def decode (x : QM) : ExactQM := AspisR1.ExtractedMaskLinearStep.decode x

def pointAtNat (point : Array QM 10#usize) (i : Nat) (hi : i < 10) : QM :=
  point.val[i]'(by simpa [point.property] using hi)

def pointValue (point : Array QM 10#usize) (i : Nat) : ExactQM :=
  if h : i < 10 then decode (pointAtNat point i h) else 0

/-- The source recurrence consumes n-1 first and then descends to 0.
    At index zero it updates only the suffix; all other indices also add the
    updated suffix into `weighted`. -/
def accumulatorModel (point : Nat → ExactQM) : Nat → ExactQM × ExactQM → ExactQM × ExactQM
  | 0, state => state
  | n + 1, (suffix, weighted) =>
      let suffix1 := suffix + point n
      accumulatorModel point n
        (suffix1, if n = 0 then weighted else weighted + suffix1)

theorem body_loop0_model (point : Array QM 10#usize) (iter : ReverseRange)
    (n : Nat) (suffix weighted : QM)
    (hstart : iter.iter.start.val = 0) (hend : iter.iter.end.val = n)
    (hn : n ≤ 10)
    (hpoint : ∀ i : Nat, ∀ hi : i < 10, CanonicalQM (pointAtNat point i hi))
    (hsuffix : CanonicalQM suffix) (hweighted : CanonicalQM weighted) :
    ∃ out : QM × QM,
      state_only_hiding.selected_mask_linears_loop iter point suffix weighted = .ok out ∧
      CanonicalQM out.1 ∧ CanonicalQM out.2 ∧
      (decode out.1, decode out.2) =
        accumulatorModel (pointValue point) n (decode suffix, decode weighted) := by
  induction n generalizing iter suffix weighted with
  | zero =>
      have hstop : iter.iter.end.val ≤ iter.iter.start.val := by omega
      refine ⟨(suffix, weighted), ?_, hsuffix, hweighted, rfl⟩
      rw [state_only_hiding.selected_mask_linears_loop, loop.eq_def]
      dsimp only
      simp only [body0_done point iter suffix weighted hstop, bind_tc_ok]
  | succ n ih =>
      have hstep : iter.iter.start.val < iter.iter.end.val := by omega
      have hendPos : 1 ≤ iter.iter.end.val := by omega
      have hidxVal : (Usize.wrapping_sub iter.iter.end 1#usize).val = n := by
        rw [wrapping_sub_one_val _ hendPos]
        omega
      have hnlt : n < 10 := by omega
      have h10 : (10#usize : Usize).val = 10 := by rfl
      have hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
          (10#usize : Usize).val := by
        rw [hidxVal, h10]
        omega
      let idx := Usize.wrapping_sub iter.iter.end 1#usize
      let q := pointAt point idx hindex
      have hget : Array.index_usize point idx = .ok q := by
        exact array_index_usize_ok point idx hindex
      have hq : CanonicalQM q := by
        simpa [q, pointAt, pointAtNat, idx, hidxVal] using hpoint n hnlt
      have hqvalue : decode q = pointValue point n := by
        simp [q, pointAt, pointAtNat, pointValue, idx, hidxVal, hnlt]
      let iter1 : ReverseRange :=
        ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩
      have hstart1 : iter1.iter.start.val = 0 := by simpa [iter1] using hstart
      have hend1 : iter1.iter.end.val = n := by
        dsimp [iter1]
        rw [wrapping_sub_one_val _ hendPos]
        omega
      by_cases hn0 : n = 0
      · have hzero : idx = 0#usize := by
          apply UScalar.eq_of_val_eq
          simp [idx, hidxVal, hn0]
        obtain ⟨suffix1, hbody, hcanon1, hvalue1⟩ :=
          body0_step_zero point iter suffix weighted q hstep hindex hzero
            hget hsuffix hweighted hq
        have hvalue1' : decode suffix1 = decode suffix + decode q := by
          simpa [decode, AspisR1.ExtractedMaskLinearStep.decode] using hvalue1
        have hrec := ih iter1 suffix1 weighted hstart1 hend1 (by omega)
          hcanon1 hweighted
        obtain ⟨out, hrun, hout0, hout1, hmodel⟩ := hrec
        rw [hn0] at hmodel ⊢
        refine ⟨out, ?_, hout0, hout1, ?_⟩
        · rw [state_only_hiding.selected_mask_linears_loop, loop.eq_def]
          dsimp only
          simp only [hbody, bind_tc_ok]
          exact hrun
        · have hstate : (decode suffix1, decode weighted) =
              (decode suffix + pointValue point 0, decode weighted) := by
            rw [hvalue1', hqvalue, hn0]
          have hmodel' := hmodel.trans
            (congrArg (accumulatorModel (pointValue point) 0) hstate)
          simpa [accumulatorModel] using hmodel'
      · have hnpos : n > 0 := by omega
        have hnzero : idx ≠ 0#usize := by
          intro h
          have hv := congrArg UScalar.val h
          rw [hidxVal] at hv
          have h0 : (0#usize).val = 0 := by rfl
          rw [h0] at hv
          omega
        obtain ⟨suffix1, weighted1, hbody, hcanon1, hcanonw1,
          hvalue1, hvaluew1⟩ :=
          body0_step_nonzero point iter suffix weighted q hstep hindex hnzero
            hget hsuffix hweighted hq
        have hvalue1' : decode suffix1 = decode suffix + decode q := by
          simpa [decode, AspisR1.ExtractedMaskLinearStep.decode] using hvalue1
        have hvaluew1' : decode weighted1 = decode weighted + decode suffix1 := by
          simpa [decode, AspisR1.ExtractedMaskLinearStep.decode] using hvaluew1
        have hrec := ih iter1 suffix1 weighted1 hstart1 hend1 (by omega)
          hcanon1 hcanonw1
        obtain ⟨out, hrun, hout0, hout1, hmodel⟩ := hrec
        refine ⟨out, ?_, hout0, hout1, ?_⟩
        · rw [state_only_hiding.selected_mask_linears_loop, loop.eq_def]
          dsimp only
          simp only [hbody, bind_tc_ok]
          exact hrun
        · have hstate : (decode suffix1, decode weighted1) =
              (decode suffix + pointValue point n,
                decode weighted + (decode suffix + pointValue point n)) := by
            rw [hvaluew1', hvalue1', hqvalue]
          have hmodel' := hmodel.trans
            (congrArg (accumulatorModel (pointValue point) n) hstate)
          simpa [accumulatorModel, hn0] using hmodel'

#print axioms body_loop0_model
end AspisR1.ExtractedMaskLinearLoop

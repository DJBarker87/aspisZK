import ExtractedMaskReverseRange
import ExtractedMaskPreparedMul

/-! Actual Aeneas one-step facts for the selected-mask reverse Horner loop.
This stops before an end-to-end loop induction or a pure-mask correspondence. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskHornerStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReverseRange
open AspisR1.ExtractedMaskPreparedState
open AspisR1.ExtractedMaskPreparedMul
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Coefficients := Aeneas.Std.Array QM 27#usize
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange

def coefficientAt (coefficients : Coefficients) (i : Usize)
    (hi : i.val < (27#usize : Usize).val) : QM :=
  coefficients.val[i.val]'(by simpa [coefficients.property] using hi)

def decode (x : QM) : AspisV8R15.ExactTowerBase.QM31Exact :=
  AspisR1.ExtractedMaskQM31Exact.decode x

/-- Checked array access at any proof-carrying in-range Usize index. This is
copied in shape from `R616MixedLimbExecution.selected_index_ok`, specialized
only by retaining the actual Aeneas array API. -/
theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Aeneas.Std.Array α n) (i : Usize) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Aeneas.Std.Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

theorem body2_done (coefficients : Coefficients) (prepared : Prepared)
    (iter : ReverseRange) (shared : QM)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    state_only_hiding.state_only_selected_mask_value_loop2.body
      coefficients prepared iter shared = .ok (.done shared) := by
  simp only [state_only_hiding.state_only_selected_mask_value_loop2.body,
    reverse_next_done iter hstop, bind_tc_ok]

theorem body2_step
    (coefficients : Coefficients) (prepared : Prepared)
    (iter : ReverseRange) (linear shared : QM)
    (hstep : iter.iter.start.val < iter.iter.end.val)
    (hindex : (Usize.wrapping_sub iter.iter.end 1#usize).val <
      (27#usize : Usize).val)
    (hlinear : CanonicalQM linear) (hshared : CanonicalQM shared)
    (hprepared : PreparedFor prepared linear)
    (hcoefficient : CanonicalQM
      (coefficientAt coefficients
        (Usize.wrapping_sub iter.iter.end 1#usize) hindex)) :
    let coefficient := coefficientAt coefficients
      (Usize.wrapping_sub iter.iter.end 1#usize) hindex
    ∃ shared1 : QM,
      state_only_hiding.state_only_selected_mask_value_loop2.body
        coefficients prepared iter shared =
          .ok (.cont
            (⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩,
              shared1)) ∧
      CanonicalQM shared1 ∧
      decode shared1 = decode linear * decode shared + decode coefficient := by
  let coefficient := coefficientAt coefficients
    (Usize.wrapping_sub iter.iter.end 1#usize) hindex
  have hidx : Array.index_usize coefficients
      (Usize.wrapping_sub iter.iter.end 1#usize) = .ok coefficient := by
    have hread := array_index_usize_ok coefficients
      (Usize.wrapping_sub iter.iter.end 1#usize) hindex
    exact hread
  obtain ⟨product, hproduct, hproductCanon, hproductValue⟩ :=
    prepared_mul_exact prepared linear shared hlinear hshared hprepared
  obtain ⟨shared1, hadd, hsharedCanon, haddValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact
      product coefficient hproductCanon hcoefficient
  refine ⟨shared1, ?_, hsharedCanon, ?_⟩
  · simp only [state_only_hiding.state_only_selected_mask_value_loop2.body,
      reverse_next_step iter hstep, bind_tc_ok, hproduct, hidx, hadd,
      bind_tc_ok]
  · simpa only [decode, hproductValue] using haddValue

#print axioms array_index_usize_ok
#print axioms body2_done
#print axioms body2_step
end AspisR1.ExtractedMaskHornerStep

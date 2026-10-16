import ExtractedMaskHornerPolynomial

/-! Constructor, seed read and reverse-range facts for the actual Horner call
site after coefficient population. Input-array canonicality remains explicit;
this theorem does not assume or prove how that array was populated. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskHornerCaller

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Coefficients := Array QM 27#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange

def decode (x : QM) : ExactQM := AspisR1.ExtractedMaskQM31Exact.decode x

def coefficientValue (coefficients : Coefficients) (i : Nat) : ExactQM :=
  if hi : i < 27 then
    decode (coefficients.val[i]'(by simpa [coefficients.property] using hi))
  else 0

def sourceRange : core.ops.range.Range Usize :=
  { start := 0#usize, «end» := state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE }

theorem prepared_seeded_horner
    (coefficients : Coefficients) (linear : QM)
    (hlinear : CanonicalQM linear)
    (hcoefficients : ∀ i : Fin 27,
      CanonicalQM (coefficients.val[i.val]'(by
        simpa [coefficients.property] using i.isLt))) :
    ∃ prepared seed iter out,
      field.PreparedQm31Multiplier.new linear = .ok prepared ∧
      Array.index_usize coefficients
        state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE = .ok seed ∧
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
        sourceRange = .ok iter ∧
      state_only_hiding.state_only_selected_mask_value_loop2
        iter coefficients prepared seed = .ok out ∧
      CanonicalQM out ∧
      decode out = AspisR1.ExtractedMaskHornerPolynomial.coefficientPolynomial
        (coefficientValue coefficients) (decode linear) := by
  obtain ⟨prepared, hnew, hprepared⟩ :=
    AspisR1.ExtractedMaskPreparedState.current_prepared_new linear hlinear
  let seed : QM := coefficients.val[26]'(by
    simpa [coefficients.property] using (show 26 < 27 by decide))
  let iter : ReverseRange := ⟨sourceRange⟩
  have hread : Array.index_usize coefficients
      state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE = .ok seed := by
    rw [state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE]
    exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      coefficients 26#usize (by decide)
  have hseed : CanonicalQM seed := hcoefficients ⟨26, by decide⟩
  have hstart : iter.iter.start.val = 0 := rfl
  have hend : iter.iter.end.val = 26 := by
    simp only [iter, sourceRange, state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE]
    rfl
  obtain ⟨out, hrun, hcanon, hmodel⟩ :=
    AspisR1.ExtractedMaskHornerLoop.body_loop2_model coefficients prepared
      linear iter 26 seed hstart hend (by omega) hlinear hprepared
      hcoefficients hseed
  change decode out = AspisR1.ExtractedMaskHornerLoop.hornerLoopModel
    (coefficientValue coefficients) (decode linear) 26 (decode seed) at hmodel
  have hseedValue : decode seed = coefficientValue coefficients 26 := by
    simp only [coefficientValue, show 26 < 27 by decide, ↓reduceDIte]
    rfl
  rw [hseedValue,
    AspisR1.ExtractedMaskHornerPolynomial.seed_coefficient_26_eq_polynomial] at hmodel
  refine ⟨prepared, seed, iter, out, hnew, hread, ?_, hrun, hcanon, hmodel⟩
  rfl

#print axioms prepared_seeded_horner
end AspisR1.ExtractedMaskHornerCaller

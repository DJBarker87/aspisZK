import CompositionPartsLoopAdapter
import TerminalHornerModel

/-! Actual candidate prepared constructor and both recursive folds, composed
with the existing 29-coefficient model. Array-to-lane correspondence remains
explicit and is NOT established by this theorem. -/
set_option autoImplicit false
namespace AspisR1.TerminalCompositionPolynomial
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalCompositionLoopAdapter
open scoped BigOperators

abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

def reverseRange (n : Usize) : ReverseRange :=
  ⟨{ start := 0#usize, «end» := n }⟩

/-- Inputs are actual fixed arrays and a copy seed. Their canonicality and
pointwise identification with semantic coefficients are caller obligations.
The multiplier constructor, both complete loops and output canonicality are
derived here; no success equation for any of those operations is assumed. -/
theorem prepared_folds_eq_lane_sum
    (semantic : Array QM 24#usize) (poseidon : Array QM 4#usize)
    (theta seed : QM) (lanes : Fin 29 → ExactQM)
    (htheta : CanonicalQM theta) (hseed : CanonicalQM seed)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt)))
    (hposeidonCanonical : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)))
    (hsemantic : ∀ i : Fin 24,
      coefficient24 semantic i.val = lanes (Fin.natAdd 4 (Fin.castAdd 1 i)))
    (hposeidon : ∀ i : Fin 4,
      coefficient4 poseidon i.val = lanes (Fin.castAdd 25 i))
    (hcopy : decode seed = lanes 28) :
    ∃ prepared : Prepared, ∃ middle out : QM,
      field.PreparedQm31Multiplier.new theta = .ok prepared ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        (reverseRange 24#usize) semantic prepared seed = .ok middle ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        (reverseRange 4#usize) poseidon prepared middle = .ok out ∧
      CanonicalQM out ∧
      decode out = ∑ i : Fin 29, decode theta ^ i.val * lanes i := by
  obtain ⟨prepared, hnew, hprepared⟩ :=
    AspisR1.ExtractedMaskPreparedState.current_prepared_new theta htheta
  obtain ⟨middle, hfirst, hmiddle, hfirstValue⟩ :=
    composition_parts_loop0_horner_model semantic prepared theta seed
      (reverseRange 24#usize) 24 rfl rfl (by omega)
      htheta hprepared hsemanticCanonical hseed
  obtain ⟨out, hsecond, hout, hsecondValue⟩ :=
    composition_parts_loop1_horner_model poseidon prepared theta middle
      (reverseRange 4#usize) 4 rfl rfl (by omega)
      htheta hprepared hposeidonCanonical hmiddle
  refine ⟨prepared, middle, out, hnew, hfirst, hsecond, hout, ?_⟩
  change AspisR1.ExtractedMaskQM31Exact.decode out = _
  rw [hsecondValue, hfirstValue,
    AspisR1.TerminalHornerModel.actual_model_eq_seeded,
    AspisR1.TerminalHornerModel.actual_model_eq_seeded]
  exact AspisR1.ExtractedMaskTerminalHorner.composeGroups_eq_lane_sum
    (decode theta) (decode seed)
    (fun i : Fin 24 => coefficient24 semantic i.val)
    (fun i : Fin 4 => coefficient4 poseidon i.val)
    lanes hposeidon hsemantic hcopy

#print axioms prepared_folds_eq_lane_sum
end AspisR1.TerminalCompositionPolynomial

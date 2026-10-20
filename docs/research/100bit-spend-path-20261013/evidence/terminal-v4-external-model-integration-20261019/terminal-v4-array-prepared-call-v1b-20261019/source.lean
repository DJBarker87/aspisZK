import TerminalV4CompositionLoopArrayPolynomialCallerV1
import TerminalV4PreparedStateCurrentV1

set_option autoImplicit false
namespace AspisR1.TerminalV4CompositionLoopArrayPreparedCall
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev decode := AspisR1.TerminalV4CompositionLoopArrayHorner.decode

/-- The real prepared-multiplier constructor and array loop compose without a
separate prepared-state or reverse-list premise. The coefficient/lane map and
pointwise canonicality of semantic entries remain explicit. -/
theorem composition_parts_loop0_after_prepared_new
    (semantic : Aeneas.Std.Array QM 24#usize) (linear seed : QM)
    (hlinear : CanonicalQM linear) (hseed : CanonicalQM seed)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt))) :
    ∃ prepared : Prepared, ∃ out : QM,
      field.PreparedQm31Multiplier.new linear = .ok prepared ∧
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨semantic.val⟩ prepared seed = .ok out ∧
      CanonicalQM out ∧
      decode out = decode seed * decode linear ^ 24 +
        ∑ i ∈ Finset.range 24,
          AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic i *
            decode linear ^ i := by
  obtain ⟨prepared, hnew, hprepared⟩ :=
    AspisR1.TerminalV4PreparedStateCurrent.current_prepared_new linear hlinear
  obtain ⟨out, hrun, hcanon, hpoly⟩ :=
    AspisR1.TerminalV4CompositionLoopArrayPolynomialCaller.composition_parts_loop0_array_polynomial_of_pointwise_canonical
      semantic prepared linear seed hlinear hprepared hseed hsemanticCanonical
  refine ⟨prepared, out, hnew, ?_, ?_, ?_⟩
  · exact hrun
  · exact hcanon
  · exact hpoly

#print axioms composition_parts_loop0_after_prepared_new
end AspisR1.TerminalV4CompositionLoopArrayPreparedCall

import TerminalV4CompositionLoopArrayPolynomialCallerV1
import TerminalV4PreparedStateCurrentV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.TerminalV4CompositionLoopArrayPreparedCall
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

/-- Construct the actual prepared multiplier, then run the checked array fold.
Pointwise entry canonicality and the source coefficient/lane bridge remain
caller obligations. -/
theorem composition_parts_loop0_after_prepared_new
    (semantic : Aeneas.Std.Array QM 24#usize) (linear seed : QM)
    (hlinear : CanonicalQM linear) (hseed : CanonicalQM seed)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt))) :
    ∃ prepared : Prepared,
      field.PreparedQm31Multiplier.new linear = .ok prepared ∧
      (∃ out : QM,
        AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
          ⟨semantic.val⟩ prepared seed = .ok out ∧
        CanonicalQM out ∧
        AspisR1.TerminalV4CompositionLoopArrayHorner.decode out =
          AspisR1.TerminalV4CompositionLoopArrayHorner.decode seed *
            AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ 24 +
          ∑ i ∈ Finset.range 24,
            AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic i *
              AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ i) := by
  obtain ⟨prepared, hnew, hprepared⟩ :=
    AspisR1.TerminalV4PreparedStateCurrent.current_prepared_new linear hlinear
  refine ⟨prepared, hnew, ?_⟩
  exact AspisR1.TerminalV4CompositionLoopArrayPolynomialCaller.composition_parts_loop0_array_polynomial_of_pointwise_canonical
    semantic prepared linear seed hlinear hprepared hseed hsemanticCanonical

#print axioms composition_parts_loop0_after_prepared_new
end AspisR1.TerminalV4CompositionLoopArrayPreparedCall

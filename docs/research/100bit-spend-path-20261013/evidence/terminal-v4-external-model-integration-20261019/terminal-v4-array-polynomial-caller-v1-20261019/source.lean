import TerminalV4CompositionLoopArrayItemsCanonicalV1

set_option autoImplicit false
namespace AspisR1.TerminalV4CompositionLoopArrayPolynomialCaller
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

 theorem composition_parts_loop0_array_polynomial_of_pointwise_canonical
    (semantic : Aeneas.Std.Array QM 24#usize)
    (prepared : field.PreparedQm31Multiplier) (linear acc : QM)
    (hlinear : CanonicalQM linear)
    (hprepared : AspisR1.TerminalV4PreparedStateCurrent.PreparedFor prepared linear)
    (hacc : CanonicalQM acc)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt))) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨semantic.val⟩ prepared acc = .ok out ∧
      CanonicalQM out ∧
      AspisR1.TerminalV4CompositionLoopArrayHorner.decode out =
        AspisR1.TerminalV4CompositionLoopArrayHorner.decode acc *
          AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ 24 +
        ∑ i ∈ Finset.range 24,
          AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic i *
            AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ i := by
  apply AspisR1.TerminalV4CompositionLoopPolynomial.composition_parts_loop0_array_polynomial
    semantic prepared linear acc hlinear hprepared hacc
  exact AspisR1.TerminalV4CompositionLoopArrayItemsCanonical.listLoopCanonicalModel_of_array
    semantic linear hsemanticCanonical

#print axioms composition_parts_loop0_array_polynomial_of_pointwise_canonical
end AspisR1.TerminalV4CompositionLoopArrayPolynomialCaller

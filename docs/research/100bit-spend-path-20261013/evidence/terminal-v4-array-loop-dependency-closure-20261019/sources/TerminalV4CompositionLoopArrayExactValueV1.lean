import TerminalV4CompositionLoopExactValueV6

set_option autoImplicit false
namespace AspisR1.TerminalV4CompositionLoopArrayExactValue
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor
abbrev decode := AspisR1.TerminalV4QM31TowerCurrent.decode

theorem composition_parts_loop0_array_exact_value
    (semantic : Aeneas.Std.Array QM 24#usize) (prepared : Prepared)
    (linear acc : QM) (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear) (hacc : CanonicalQM acc)
    (hitems : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel
      linear (semantic.val.reverse)) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨semantic.val⟩ prepared acc = .ok out ∧
      CanonicalQM out ∧
      decode out = AspisR1.TerminalV4CompositionLoopExactValue.listHorner
        (decode linear) semantic.val.reverse (decode acc) := by
  obtain ⟨out, hrun, hcanon, hvalue⟩ :=
    AspisR1.TerminalV4CompositionLoopExactValue.composition_parts_loop0_exact_value
      (items := semantic.val.reverse) prepared linear acc hlinear hprepared hacc hitems
  refine ⟨out, ?_, hcanon, hvalue⟩
  simpa only [List.reverse_reverse] using hrun

#print axioms composition_parts_loop0_array_exact_value
end AspisR1.TerminalV4CompositionLoopArrayExactValue

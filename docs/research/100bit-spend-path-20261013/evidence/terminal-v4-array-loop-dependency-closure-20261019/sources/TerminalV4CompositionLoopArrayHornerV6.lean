import TerminalV4CompositionLoopArrayExactValueV1
import TerminalV4CompositionLoopHornerBridgeV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.TerminalV4CompositionLoopArrayHorner
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor
abbrev ExactQM := AspisV8R17.QM31WordTower.Q
abbrev decode := AspisR1.TerminalV4QM31TowerCurrent.decode

def coefficient24 (a : Aeneas.Std.Array QM 24#usize) (i : Nat) : ExactQM :=
  if hi : i < 24 then
    decode (a.val[i]'(by simpa [a.property] using hi))
  else 0

attribute [local irreducible]
  coefficient24 AspisR1.TerminalV4CompositionLoopHornerBridge.listCoefficient
  AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner

theorem listCoefficient_eq_coefficient24
    (semantic : Aeneas.Std.Array QM 24#usize) :
    ∀ i < 24,
      AspisR1.TerminalV4CompositionLoopHornerBridge.listCoefficient
        semantic.val.reverse i = coefficient24 semantic i := by
  intro i hi
  simp [AspisR1.TerminalV4CompositionLoopHornerBridge.listCoefficient,
    coefficient24, List.reverse_reverse, hi, semantic.property]

theorem composition_parts_loop0_array_horner
    (semantic : Aeneas.Std.Array QM 24#usize) (prepared : Prepared)
    (linear acc : QM) (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear) (hacc : CanonicalQM acc)
    (hitems : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel
      linear (semantic.val.reverse)) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨semantic.val⟩ prepared acc = .ok out ∧
      CanonicalQM out ∧
      decode out = AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner
        (coefficient24 semantic) (decode linear) 24 (decode acc) := by
  obtain ⟨out, hrun, hcanon, hvalue⟩ :=
    AspisR1.TerminalV4CompositionLoopArrayExactValue.composition_parts_loop0_array_exact_value
      semantic prepared linear acc hlinear hprepared hacc hitems
  refine ⟨out, hrun, hcanon, ?_⟩
  change AspisR1.TerminalV4CompositionLoopArrayExactValue.decode out =
    AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner
      (coefficient24 semantic)
      (AspisR1.TerminalV4CompositionLoopArrayExactValue.decode linear) 24
      (AspisR1.TerminalV4CompositionLoopArrayExactValue.decode acc)
  have hlen : semantic.val.reverse.length = 24 := by
    simp only [List.length_reverse]
    simpa [semantic.property]
  rw [hvalue, AspisR1.TerminalV4CompositionLoopHornerBridge.listHorner_eq_natHorner]
  rw [hlen]
  have hcoeff : ∀ i < 24,
      AspisR1.TerminalV4CompositionLoopHornerBridge.listCoefficient
        semantic.val.reverse i = coefficient24 semantic i :=
    listCoefficient_eq_coefficient24 semantic
  exact AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner_congr_below
    (AspisR1.TerminalV4CompositionLoopHornerBridge.listCoefficient semantic.val.reverse)
    (coefficient24 semantic) (decode linear) (decode acc) 24 hcoeff

#print axioms listCoefficient_eq_coefficient24
#print axioms composition_parts_loop0_array_horner
end AspisR1.TerminalV4CompositionLoopArrayHorner

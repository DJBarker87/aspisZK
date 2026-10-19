import TerminalV4CompositionLoopArrayHornerV6
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.TerminalV4CompositionLoopPolynomial
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev ExactQM := AspisV8R17.QM31WordTower.Q
abbrev decode := AspisR1.TerminalV4QM31TowerCurrent.decode

theorem natHorner_eq_sum (coefficients : Nat → ExactQM)
    (linear acc : ExactQM) (n : Nat) :
    AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner coefficients linear n acc =
      acc * linear ^ n + ∑ i ∈ Finset.range n, coefficients i * linear ^ i := by
  induction n generalizing acc with
  | zero => simp [AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner]
  | succ n ih =>
      rw [AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner.eq_2]
      rw [ih, Finset.sum_range_succ, pow_succ]
      ring

theorem composition_parts_loop0_array_polynomial
    (semantic : Aeneas.Std.Array field.QM31 24#usize)
    (prepared : field.PreparedQm31Multiplier) (linear acc : field.QM31)
    (hlinear : AspisR1.TerminalV4TowerAdd.CanonicalQM linear)
    (hprepared : AspisR1.TerminalV4PreparedStateCurrent.PreparedFor prepared linear)
    (hacc : AspisR1.TerminalV4TowerAdd.CanonicalQM acc)
    (hitems : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel
      linear semantic.val.reverse) :
    ∃ out : field.QM31,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        ⟨semantic.val⟩ prepared acc = .ok out ∧
      AspisR1.TerminalV4TowerAdd.CanonicalQM out ∧
      AspisR1.TerminalV4CompositionLoopArrayHorner.decode out =
        AspisR1.TerminalV4CompositionLoopArrayHorner.decode acc *
          AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ 24 +
        ∑ i ∈ Finset.range 24,
          AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic i *
            AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ i := by
  obtain ⟨out, hrun, hcanon, hvalue⟩ :=
    AspisR1.TerminalV4CompositionLoopArrayHorner.composition_parts_loop0_array_horner
      semantic prepared linear acc hlinear hprepared hacc hitems
  refine ⟨out, hrun, hcanon, ?_⟩
  calc
    AspisR1.TerminalV4CompositionLoopArrayHorner.decode out =
        AspisR1.TerminalV4CompositionLoopHornerBridge.natHorner
          (AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic)
          (AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear) 24
          (AspisR1.TerminalV4CompositionLoopArrayHorner.decode acc) := hvalue
    _ = AspisR1.TerminalV4CompositionLoopArrayHorner.decode acc *
          AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ 24 +
          ∑ i ∈ Finset.range 24,
            AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic i *
              AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear ^ i :=
      natHorner_eq_sum (AspisR1.TerminalV4CompositionLoopArrayHorner.coefficient24 semantic)
        (AspisR1.TerminalV4CompositionLoopArrayHorner.decode linear)
        (AspisR1.TerminalV4CompositionLoopArrayHorner.decode acc) 24

#print axioms natHorner_eq_sum
#print axioms composition_parts_loop0_array_polynomial
end AspisR1.TerminalV4CompositionLoopPolynomial

import TerminalV4QM31ExactV5
import Mathlib.Tactic.NormNum

/-! Literal zero/one facts for the current generated QM31 representation. -/
set_option autoImplicit false

namespace AspisR1.TerminalV4Constants

open Aeneas Aeneas.Std

abbrev CanonicalQM := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

 theorem zero_canonical : CanonicalQM AspisR1SelectedMaskProbe.field.QM31.ZERO := by
  simp [CanonicalQM, AspisR1.TerminalV4TowerAdd.CanonicalQM,
    AspisR1.TerminalV4TowerAdd.CanonicalCM,
    AspisR1SelectedMaskProbe.field.QM31.ZERO,
    AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P]

theorem zero_decode :
    AspisR1.TerminalV4QM31Exact.decode AspisR1SelectedMaskProbe.field.QM31.ZERO = (0 : ExactQM) := by
  ext <;> simp [AspisR1.TerminalV4QM31Exact.decode,
    AspisR1SelectedMaskProbe.field.QM31.ZERO]

theorem one_canonical : CanonicalQM AspisR1SelectedMaskProbe.field.QM31.ONE := by
  norm_num [CanonicalQM, AspisR1.TerminalV4TowerAdd.CanonicalQM,
    AspisR1.TerminalV4TowerAdd.CanonicalCM,
    AspisR1SelectedMaskProbe.field.QM31.ONE,
    AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P]

theorem one_decode :
    AspisR1.TerminalV4QM31Exact.decode AspisR1SelectedMaskProbe.field.QM31.ONE = (1 : ExactQM) := by
  ext <;> simp [AspisR1.TerminalV4QM31Exact.decode,
    AspisR1SelectedMaskProbe.field.QM31.ONE,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

#print axioms zero_canonical
#print axioms zero_decode
#print axioms one_canonical
#print axioms one_decode

end AspisR1.TerminalV4Constants

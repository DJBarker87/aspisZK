import TerminalV4CurrentArithmeticInstantiationV1
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe.TerminalV4RunShapeProbe
abbrev QM := field.QM31
def runCopy (q composition h1Z copyActive mu : QM) : Result QM := do
  let q1 ← field.QM31.mul q composition
  let q2 ← field.QM31.mul mu h1Z
  let q3 ← field.QM31.add q1 q2
  let q4 ← field.QM31.mul mu mu
  let q5 ← field.QM31.sub field.QM31.ONE copyActive
  let q6 ← field.QM31.mul q5 h1Z
  let q7 ← field.QM31.mul q4 q6
  field.QM31.add q3 q7
theorem shape (q composition h1Z copyActive mu : QM) :
  AspisR1SelectedMaskProbe.TerminalV4CurrentArithmeticContract.run q composition h1Z copyActive mu =
  runCopy q composition h1Z copyActive mu := rfl
end AspisR1SelectedMaskProbe.TerminalV4RunShapeProbe

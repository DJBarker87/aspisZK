import AspisR1RhoPowerTail.Types
import ExtractedCurrentQM31Mul
open Aeneas Aeneas.Std Result
namespace AspisR1RhoPowerTail
abbrev Current := AspisR1Qm31ArithmeticProbe.field.QM31
def toCurrent (x : aspis_core.field.QM31) : Current :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}
def fromCurrent (x : Current) : aspis_core.field.QM31 :=
  {c0 := {a := x.c0.a,b := x.c0.b},c1 := {a := x.c1.a,b := x.c1.b}}
-- Exact existing source function with coordinate-only carrier transport.
def aspis_core.field.QM31.mul (x y : aspis_core.field.QM31) :
    Result aspis_core.field.QM31 := do
  let out ← AspisR1Qm31ArithmeticProbe.field.QM31.mul (toCurrent x) (toCurrent y)
  pure (fromCurrent out)
end AspisR1RhoPowerTail

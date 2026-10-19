import AspisR1RhoReferenceLoop.Types
import CuSavingsRhoReference
import AspisR1RhoDiagnostics.Funs

/-! Bind shared arithmetic to the already checked reference kernels and shared
constructors/trace to the complete exact source emission. No template axioms. -/
namespace AspisR1RhoCoefficients
open Aeneas Aeneas.Std Result
open AspisR1.CuSavingsRhoReference

def QM31.mul_m31 (power : aspis_core.field.QM31) (basis : U32) :
    Result aspis_core.field.QM31 := do
  let out ← AspisR1RhoReference.field.QM31.mul_m31 (toCurrent power) basis
  .ok (fromCurrent out)

def aspis_core.field.QM31.add (left right : aspis_core.field.QM31) :
    Result aspis_core.field.QM31 := do
  let out ← AspisR1Qm31ArithmeticProbe.field.QM31.add (toCurrent left) (toCurrent right)
  .ok (fromCurrent out)

abbrev aspis_core.field.WideExact.from_qm31 := AspisR1CuRho.field.WideExact.from_qm31
abbrev aspis_core.field.WideExact.from_m31 := AspisR1CuRho.from_m31
abbrev trace.value := AspisR1CuRho.trace.value
end AspisR1RhoCoefficients

import AspisR1RhoAccumulate.Types
import AspisR1RhoOptimizedLoop.Funs
import AspisR1RhoReferenceLoop.Funs
import AspisR1RhoBasis.Funs
import AspisR1RhoPowerTail.FunsExternal
namespace AspisR1RhoAccumulate
open Aeneas Aeneas.Std Result
open AspisR1.CuSavingsRhoReference

/- Unchanged RHS operations are common arbitrary computations. There is no
propositional equivalence, success, termination, or canonicality assumption. -/
class AccumulateCommon where
  mulQm31 : aspis_core.field.WideExact → aspis_core.field.QM31 → Result aspis_core.field.WideExact
  add : aspis_core.field.WideExact → aspis_core.field.WideExact → Result aspis_core.field.WideExact
abbrev WideExact.mul_qm31 [AccumulateCommon] := AccumulateCommon.mulQm31
abbrev aspis_core.field.WideExact.add [AccumulateCommon] := AccumulateCommon.add

def aspis_core.field.QM31.mul (x y : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let out ← AspisR1Qm31ArithmeticProbe.field.QM31.mul (toCurrent x) (toCurrent y)
  .ok (fromCurrent out)

abbrev rho_old.coefficients := AspisR1RhoCoefficients.rho_old.coefficients
abbrev rho_new.coefficients := AspisR1RhoCoefficients.rho_new.coefficients
abbrev source_basis_old := AspisR1RhoBasis.basis
abbrev source_basis_new := AspisR1RhoBasis.basis
abbrev trace.value := AspisR1CuRho.trace.value
end AspisR1RhoAccumulate

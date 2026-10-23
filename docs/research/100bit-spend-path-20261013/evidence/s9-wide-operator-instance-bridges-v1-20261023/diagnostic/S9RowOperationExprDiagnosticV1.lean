import S9ScalarConstructorModelV1
import S9SymbolicRowTransportV1
import Lean
set_option autoImplicit false
open Lean Elab Command
namespace S9RowOperationExprDiagnosticV1
abbrev E := AspisWideTower.WideExact
noncomputable def specializedShape (alpha : E) (a : Fin 4 → E) : E :=
  AspisR1S9SymbolicRowTransportV1.shape alpha a AspisR1S9ScalarActualPowerPolynomialV1.quarter
noncomputable def sourceMul (x y : E) : E := x*y
noncomputable def sourcePow (x : E) : E := x^3
noncomputable def sourceZero : E := 0
noncomputable def sourceInv (x : E) : E := x⁻¹
noncomputable def genericMul {K : Type} [Field K] (x y : K) : K := x*y
noncomputable def genericPow {K : Type} [Field K] (x : K) : K := x^3
noncomputable def genericZero {K : Type} [Field K] : K := 0
noncomputable def genericInv {K : Type} [Field K] (x : K) : K := x⁻¹
noncomputable def specializedMul (x y : E) : E := genericMul x y
noncomputable def specializedPow (x : E) : E := genericPow x
noncomputable def specializedZero : E := genericZero
noncomputable def specializedInv (x : E) : E := genericInv x
end S9RowOperationExprDiagnosticV1
run_elab do
  let names : Array Name := #[
    `AspisR1S9ScalarConstructorModelV1.factorPolynomial,
    `AspisR1S9SymbolicRowTransportV1.shape,
    `S9RowOperationExprDiagnosticV1.specializedShape,
    `S9RowOperationExprDiagnosticV1.sourceMul,
    `S9RowOperationExprDiagnosticV1.genericMul,
    `S9RowOperationExprDiagnosticV1.specializedMul,
    `S9RowOperationExprDiagnosticV1.sourcePow,
    `S9RowOperationExprDiagnosticV1.genericPow,
    `S9RowOperationExprDiagnosticV1.specializedPow,
    `S9RowOperationExprDiagnosticV1.sourceZero,
    `S9RowOperationExprDiagnosticV1.genericZero,
    `S9RowOperationExprDiagnosticV1.specializedZero,
    `S9RowOperationExprDiagnosticV1.sourceInv,
    `S9RowOperationExprDiagnosticV1.genericInv,
    `S9RowOperationExprDiagnosticV1.specializedInv]
  names.forM fun n => do
    let c ← getConstInfo n
    logInfo s!"EXPR|{n}|{reprStr (c.value? true)}"

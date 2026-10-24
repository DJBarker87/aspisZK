import S9PointRowTwoFoldV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9PointRowDualFoldModelV1
open AspisR1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
open Lean
def canonicalName (n : Name) : Name :=
  if #[`AspisR1S9PointExactOperatorTransportV1.E,`AspisR1S9PointNativeMulProjectionV1.E,`AspisR1S9ScalarConstructorModelV1.E,`AspisR1S9PointRowDualFoldModelV1.E,
       `AspisR1S9WideMulOperatorBridgeV1.E,`AspisR1S9ScalarActualPowerPolynomialV1.E,
       `AspisR1S9SharedScalarModelValuesV1.E].contains n then `AspisWideTower.WideExact
  else if #[`S9SourceShapeExprDiagnosticV1.Q,`AspisR1S9SharedScalarModelValuesV1.ExactQM].contains n then
    `AspisR1CurrentWide.Proof.ExactQM
  else n
partial def firstDifference (p : String) (a b : Expr) : Option (String × Expr × Expr) :=
  if a == b then none else
  match a,b with
  | .const n us,.const m vs => if canonicalName n==canonicalName m && us==vs then none else some (p,a,b)
  | .app f x,.app g y => (firstDifference (p++".fn") f g).orElse fun _ => firstDifference (p++".arg") x y
  | .lam _ t x bi,.lam _ u y bj => if bi != bj then some (p,a,b) else
      (firstDifference (p++".lamTy") t u).orElse fun _ => firstDifference (p++".lamBody") x y
  | .forallE _ t x bi,.forallE _ u y bj => if bi != bj then some (p,a,b) else
      (firstDifference (p++".forallTy") t u).orElse fun _ => firstDifference (p++".forallBody") x y
  | .proj n i x,.proj m j y => if n==m && i==j then firstDifference (p++".proj") x y else some (p,a,b)
  | _,_ => some (p,a,b)


/-- The actual source-buffer field observation vector is kept fixed. Its
constructor-model rowValue equals the model's precise two-fold dual dot.
This transports the optimized point-part expression, not an independently
chosen coefficient/input vector. -/
example (model : Table) (k : Nat) (a0 a1 : E) (f : Slice U8) : True := by
  have hd := AspisR1S9SymbolicRowTransportV1.dot_scaled_transport
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
    (RoundPairing.dualFold a1
      (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j))))
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i => (point_row_two_dual_folds model k a0 a1 i).trans
      (AspisR1S9PointNativeMulProjectionV1.native_mul_projected _ _))
  have hs := AspisR1S9PointExactOperatorTransportV1.scaled_sum_operator_eq
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
  dsimp only [AspisR1S9PointExactOperatorTransportV1.fieldScaledSum] at hs
  run_tac Lean.Elab.Tactic.withMainContext do
    let ds ← Lean.Meta.getLocalDeclFromUserName `hs
    let dd ← Lean.Meta.getLocalDeclFromUserName `hd
    let s ← Lean.instantiateMVars ds.type
    let d ← Lean.instantiateMVars dd.type
    let sr := s.getAppArgs[2]!
    let dr := d.getAppArgs[2]!
    Lean.logInfo s!"HS-RHS {repr sr}"
    Lean.logInfo s!"HD-RHS {repr dr}"
    match firstDifference "rhs" sr dr with
    | none => Lean.logInfo "FIRSTDIFF NONE (explicit E-alias-name comparison only)"
    | some (p,x,y) =>
      Lean.logInfo s!"FIRSTDIFF-PATH {p}"
      Lean.logInfo s!"FIRSTDIFF-HS {repr x}"
      Lean.logInfo s!"FIRSTDIFF-HD {repr y}"
  trivial
end AspisR1S9PointRowDualFoldModelV1

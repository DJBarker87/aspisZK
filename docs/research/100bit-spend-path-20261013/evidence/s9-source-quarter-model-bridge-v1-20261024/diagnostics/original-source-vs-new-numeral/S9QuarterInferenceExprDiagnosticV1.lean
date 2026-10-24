import S9SourceQuarterInverseV1
import S9WideFieldOperatorBridgesV1
import RoundPairing
import Lean
set_option autoImplicit false
open Lean Elab Command
namespace S9SourceShapeExprDiagnosticV1
/-- Pure syntax expansion of TWO explicitly allowed wrappers and beta only.
No whnf, instance projection, field operation or numerical reduction. -/
partial def expandSelected (env : Environment) (e : Expr) : Expr := Id.run do
  let e := e.headBeta
  let fn := e.getAppFn
  if let .const n us := fn then
    if n == `S9SourceShapeExprDiagnosticV1.operatorShape ||
       n == `AspisR1S9WideMulOperatorBridgeV1.concreteMul then
      if let some ci := env.find? n then
        if let some value := ci.value? true then
          return expandSelected env (mkAppN (value.instantiateLevelParams ci.levelParams us) e.getAppArgs)
  match e with
  | .app f a => return (mkApp (expandSelected env f) (expandSelected env a)).headBeta
  | .lam n t b bi => return .lam n (expandSelected env t) (expandSelected env b) bi
  | .forallE n t b bi => return .forallE n (expandSelected env t) (expandSelected env b) bi
  | .letE n t v b nd => return .letE n (expandSelected env t) (expandSelected env v) (expandSelected env b) nd
  | .mdata _ b => return expandSelected env b
  | .proj n i b => return .proj n i (expandSelected env b)
  | _ => return e

def canonicalName (n : Name) : Name :=
  if #[`AspisR1S9ScalarConstructorModelV1.E,`S9SourceShapeExprDiagnosticV1.E,
       `AspisR1S9WideMulOperatorBridgeV1.E,`AspisR1S9ScalarActualPowerPolynomialV1.E,
       `AspisR1S9SharedScalarModelValuesV1.E,`AspisR1S9SourceQuarterInverseV1.E,
       `S9QuarterInferenceExprDiagnosticV1.E].contains n then `AspisWideTower.WideExact
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
end S9SourceShapeExprDiagnosticV1
namespace S9QuarterInferenceExprDiagnosticV1
abbrev E := AspisWideTower.WideExact
noncomputable def expectedBare : Prop :=
  AspisR1S9ScalarActualPowerPolynomialV1.quarter=((4 : AspisWideTower.WideExact)⁻¹)
noncomputable def expectedAlias : Prop :=
  AspisR1S9ScalarActualPowerPolynomialV1.quarter=((4 : E)⁻¹)
end S9QuarterInferenceExprDiagnosticV1
run_elab do
  let env ← getEnv
  let src ← getConstInfo `AspisR1S9SourceQuarterInverseV1.source_quarter_eq_inverse_four
  let bc ← getConstInfo `S9QuarterInferenceExprDiagnosticV1.expectedBare
  let ac ← getConstInfo `S9QuarterInferenceExprDiagnosticV1.expectedAlias
  let some bare := bc.value? true | throwError "bare body absent"
  let some aliasedExpr := ac.value? true | throwError "aliasedExpr body absent"
  let source := S9SourceShapeExprDiagnosticV1.expandSelected env src.type
  let bare := S9SourceShapeExprDiagnosticV1.expandSelected env bare
  let aliasedExpr := S9SourceShapeExprDiagnosticV1.expandSelected env aliasedExpr
  logInfo s!"Q-SOURCE {repr source}"
  logInfo s!"Q-BARE {repr bare}"
  logInfo s!"Q-ALIAS {repr aliasedExpr}"
  let pairs : Array (String × Expr × Expr) := #[
    ("SOURCE-BARE",source,bare),("SOURCE-ALIAS",source,aliasedExpr),("ALIAS-BARE",aliasedExpr,bare)]
  pairs.forM fun (tag,x,y) => do
    match S9SourceShapeExprDiagnosticV1.firstDifference "root" x y with
    | none => logInfo s!"QDIFF|{tag}|NONE after transparent type aliases"
    | some (p,a,b) =>
      logInfo s!"QDIFF|{tag}|{p}"
      logInfo s!"QDIFF-LHS|{tag}|{repr a}"
      logInfo s!"QDIFF-RHS|{tag}|{repr b}"

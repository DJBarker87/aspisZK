import S9WideMulOperatorBridgeV1
import S9ScalarConstructorModelV1
import Lean
set_option autoImplicit false
open Lean Elab Command
namespace S9SourceShapeExprDiagnosticV1
abbrev E := AspisWideTower.WideExact
abbrev Q := AspisR1S9SharedScalarModelValuesV1.ExactQM
def operatorShape {K : Type} (z : K) (add mul : K → K → K)
    (pow : K → Nat → K) (alpha : K) (a : Fin 4 → K) (q : K) : K :=
  mul (add (add (add (add z (mul (pow alpha 0) (a 0)))
    (mul (pow alpha 3) (a 1))) (mul (pow alpha 2) (a 2)))
    (mul (pow alpha 1) (a 3))) q
noncomputable def sourceOperatorValue (alpha : E) (a : Nat → Q) : E :=
  operatorShape (0 : E) (fun x y => x+y)
    AspisR1S9WideMulOperatorBridgeV1.concreteMul (fun x n => x^n)
    alpha (fun t : Fin 4 => AspisR1S9SharedScalarModelValuesV1.embedQ (a t.val))
    AspisR1S9ScalarActualPowerPolynomialV1.quarter
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
       `AspisR1S9WideMulOperatorBridgeV1.E].contains n then `AspisWideTower.WideExact
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
run_elab do
  let env ← getEnv
  let ca ← getConstInfo `AspisR1S9ScalarConstructorModelV1.factorPolynomial
  let cb ← getConstInfo `S9SourceShapeExprDiagnosticV1.sourceOperatorValue
  let some a := ca.value? true | throwError "source body absent"
  let some b := cb.value? true | throwError "comparison body absent"
  let aa := S9SourceShapeExprDiagnosticV1.expandSelected env a
  let bb := S9SourceShapeExprDiagnosticV1.expandSelected env b
  logInfo s!"SOURCE-EXPANDED {repr aa}"
  logInfo s!"WRAPPER-EXPANDED {repr bb}"
  match S9SourceShapeExprDiagnosticV1.firstDifference "root" aa bb with
  | none => logInfo "FIRSTDIFF NONE after explicit type-alias-name canonicalization"
  | some (p,x,y) =>
    logInfo s!"FIRSTDIFF-PATH {p}"
    logInfo s!"FIRSTDIFF-SOURCE {repr x}"
    logInfo s!"FIRSTDIFF-WRAPPER {repr y}"

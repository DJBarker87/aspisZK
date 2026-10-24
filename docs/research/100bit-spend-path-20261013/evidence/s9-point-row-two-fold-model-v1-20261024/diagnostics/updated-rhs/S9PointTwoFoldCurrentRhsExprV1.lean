import S9SharedHighConstructorModelV1
import S9TwoFoldProductModelV1
import S9SymbolicRowTransportV1
import S9SourceFactorShapeTransportV1
import S9SourceQuarterModelBridgeV1
import S9OpaqueQEmbedTripleV1
import S9PointExactOperatorTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9PointRowDualFoldModelV1
open AspisR1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
abbrev E := AspisWideTower.WideExact
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

abbrev highProduct := AspisR1S9ConstructorTableNativeTensorV1.highProduct

/-- The five radix-four factors of ONE constructor table row. This is a
model expression; correspondence to a public functional is supplied by the
complete same-constructor statement/circle semantics. -/
def rawRow (model : Table) (k : Nat) (j : Fin 1024) : ExactQM :=
  model k 0 (j.val%4)*model k 1 ((j.val/4)%4)*highProduct (model k) (j.val/16)

theorem rawRow_children (model : Table) (k : Nat) (d : Fin 64) (t1 t0 : Fin 4) :
    rawRow model k (childIndex (childIndex d t1) t0)=
      model k 0 t0.val*model k 1 t1.val*highProduct (model k) d.val := by
  unfold rawRow
  simp only [childIndex_val]
  have h0 : (4*(4*d.val+t1.val)+t0.val)%4=t0.val := by
    have := t0.isLt; have := t1.isLt; omega
  have h1 : ((4*(4*d.val+t1.val)+t0.val)/4)%4=t1.val := by
    have := t0.isLt; have := t1.isLt; omega
  have h2 : (4*(4*d.val+t1.val)+t0.val)/16=d.val := by
    have := t0.isLt; have := t1.isLt; omega
  rw [h0,h1,h2]

theorem factor_model_eq (alpha : E) (a : Nat → ExactQM) :
    AspisR1S9TwoFoldProductModelV1.factor alpha (fun t : Fin 4 => embedQ (a t.val))=
      factorPolynomial alpha a := by
  have hl := AspisR1S9SymbolicRowTransportV1.factor_shape alpha
    (fun t : Fin 4 => embedQ (a t.val))
  have hq : (RoundPairing.quarter : E)=AspisR1S9ScalarActualPowerPolynomialV1.quarter :=
    AspisR1S9SourceQuarterModelBridgeV1.source_quarter_eq_model_quarter.symm
  have hc := AspisR1S9SymbolicRowTransportV1.shape_quarter_congr alpha
    (fun t : Fin 4 => embedQ (a t.val)) RoundPairing.quarter
    AspisR1S9ScalarActualPowerPolynomialV1.quarter hq
  exact hl.trans (hc.trans (AspisR1S9SourceFactorShapeTransportV1.source_factor_eq_generic_shape alpha a).symm)

theorem embedded_raw_children (model : Table) (k : Nat) (d : Fin 64) (t1 t0 : Fin 4) :
    embedQ (rawRow model k (childIndex (childIndex d t1) t0))=
      (embedQ (model k 0 t0.val)*embedQ (model k 1 t1.val))*
        embedQ (highProduct (model k) d.val) := by
  have hr := congrArg embedQ (rawRow_children model k d t1 t0)
  have hm := AspisR1S9OpaqueQEmbedTripleV1.embedQ_triple
    (model k 0 t0.val) (model k 1 t1.val) (highProduct (model k) d.val)
  exact hr.trans hm

/-- Two model dual folds of the row are exactly the source scalar factors
and its remaining high product. Existing four-child Horner algebra is reused;
no 1024-cell concrete expansion is evaluated. -/
example (model : Table) (k : Nat) (a0 a1 : E) (d : Fin 64) : True := by
  have hh := AspisR1S9TwoFoldProductModelV1.two_dual_fold_child_product (n := 64)
    a0 a1 (fun j => embedQ (rawRow model k j))
    (fun t : Fin 4 => embedQ (model k 0 t.val))
    (fun t : Fin 4 => embedQ (model k 1 t.val))
    (fun d : Fin 64 => embedQ (highProduct (model k) d.val)) d
    (fun t1 t0 => (embedded_raw_children model k d t1 t0).trans
      (AspisR1S9PointExactOperatorTransportV1.triple_operator_eq
        (embedQ (model k 0 t0.val)) (embedQ (model k 1 t1.val))
        (embedQ (highProduct (model k) d.val))))
  have he := congrArg₂ (fun x y : E => x*y)
    (factor_model_eq a0 (model k 0)) (factor_model_eq a1 (model k 1))
  have ht := AspisR1S9PointExactOperatorTransportV1.triple_operator_eq
    (AspisR1S9TwoFoldProductModelV1.factor a0 (fun t : Fin 4 => embedQ (model k 0 t.val)))
    (AspisR1S9TwoFoldProductModelV1.factor a1 (fun t : Fin 4 => embedQ (model k 1 t.val)))
    (embedQ (highProduct (model k) d.val))
  dsimp only [AspisR1S9PointExactOperatorTransportV1.fieldTriple] at ht
  run_tac Lean.Elab.Tactic.withMainContext do
    let dh ← Lean.Meta.getLocalDeclFromUserName `hh
    let dt ← Lean.Meta.getLocalDeclFromUserName `ht
    let h ← Lean.instantiateMVars dh.type
    let t ← Lean.instantiateMVars dt.type
    let hr := h.getAppArgs[2]!
    let tr := t.getAppArgs[2]!
    Lean.logInfo s!"HH-RHS {repr hr}"
    Lean.logInfo s!"HT-RHS {repr tr}"
    match firstDifference "rhs" hr tr with
    | none => Lean.logInfo "FIRSTDIFF NONE (explicit E-alias-name comparison only)"
    | some (p,x,y) =>
      Lean.logInfo s!"FIRSTDIFF-PATH {p}"
      Lean.logInfo s!"FIRSTDIFF-HH {repr x}"
      Lean.logInfo s!"FIRSTDIFF-HT {repr y}"
  trivial
end AspisR1S9PointRowDualFoldModelV1

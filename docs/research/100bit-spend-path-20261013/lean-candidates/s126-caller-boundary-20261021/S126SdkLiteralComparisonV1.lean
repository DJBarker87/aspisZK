import Lean
open Lean
namespace AspisS126SdkLiteral
def sameDeclarationAlphaMetadata (a b : ConstantInfo) : Bool :=
  match a, b with
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | .inductInfo a, .inductInfo b =>
      a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false

/-- Exact expression equality; binder names and binder annotations retained. -/
def sameExprOption : Option Expr → Option Expr → Bool
  | none,none => true
  | some a,some b => Expr.equal a b
  | _,_ => false

def sameRecursorRhs (a b : ConstantInfo) : Bool :=
  match a,b with
  | .recInfo a,.recInfo b =>
    a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all (fun (r,s) => Expr.equal r.rhs s.rhs)
  | _,_ => true

/-- Original full metadata checks PLUS every expression-bearing field checked
with Expr.equal. No rewriting, alpha normalization or proof erasure. -/
def sameDeclarationLiteral (a b : ConstantInfo) : Bool :=
  sameDeclarationAlphaMetadata a b && Expr.equal a.type b.type &&
    sameExprOption (a.value? (allowOpaque := true)) (b.value? (allowOpaque := true)) &&
    sameRecursorRhs a b

private def test : IO Unit := do
  let x := Expr.lam `x (.sort .zero) (.bvar 0) .default
  let y := Expr.lam `y (.sort .zero) (.bvar 0) .default
  let implicitX := Expr.lam `x (.sort .zero) (.bvar 0) .implicit
  unless (x == y) && !(Expr.equal x y) do throw (IO.userError "binder-name counterexample missing")
  unless (x == implicitX) && !(Expr.equal x implicitX) do throw (IO.userError "binder-annotation counterexample missing")
  -- Synthetic ConstantInfo DATA, never inserted in an environment or used as a proof.
  let opaqueA : ConstantInfo := .opaqueInfo {name:=`Synthetic,levelParams:=[],type:=.sort .zero,value:=x,isUnsafe:=false}
  let opaqueB : ConstantInfo := .opaqueInfo {name:=`Synthetic,levelParams:=[],type:=.sort .zero,value:=y,isUnsafe:=false}
  unless sameDeclarationAlphaMetadata opaqueA opaqueB && !sameDeclarationLiteral opaqueA opaqueB do
    throw (IO.userError "opaque full-value guard failed")
  let recA : ConstantInfo := .recInfo {
    name := `SyntheticRec
    levelParams := []
    type := .sort .zero
    all := [`Synthetic]
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 1
    rules := [{ctor := `Synthetic.mk, nfields := 0, rhs := x}]
    k := false
    isUnsafe := false}
  let recB : ConstantInfo := .recInfo {
    name := `SyntheticRec
    levelParams := []
    type := .sort .zero
    all := [`Synthetic]
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 1
    rules := [{ctor := `Synthetic.mk, nfields := 0, rhs := y}]
    k := false
    isUnsafe := false}
  unless sameDeclarationAlphaMetadata recA recB && !sameDeclarationLiteral recA recB do
    throw (IO.userError "recursor rule RHS guard failed")
  let unsafeOpaque : ConstantInfo := .opaqueInfo {name:=`Synthetic,levelParams:=[],type:=.sort .zero,value:=x,isUnsafe:=true}
  unless !sameDeclarationLiteral opaqueA unsafeOpaque do throw (IO.userError "metadata guard lost")
  unless sameDeclarationLiteral opaqueA opaqueA && sameDeclarationLiteral recA recA do
    throw (IO.userError "reflexive data comparisons failed")
  IO.println "LITERAL_COMPARATOR_TEST PASS binder_name binder_annotation opaque_value recursor_rhs metadata reflexivity; synthetic data only"
#eval test

end AspisS126SdkLiteral

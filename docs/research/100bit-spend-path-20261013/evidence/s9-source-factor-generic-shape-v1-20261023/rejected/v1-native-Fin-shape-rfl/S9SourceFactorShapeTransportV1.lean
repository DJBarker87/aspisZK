import S9WideFieldOperatorBridgesV1
import S9SymbolicRowTransportV1
set_option autoImplicit false
namespace AspisR1S9SourceFactorShapeTransportV1
open AspisR1S9WideMulOperatorBridgeV1 (concreteMul fieldMul mul_operator_eq)
open AspisR1S9WideFieldOperatorBridgesV1
abbrev E := AspisWideTower.WideExact
abbrev Q := AspisR1S9SharedScalarModelValuesV1.ExactQM

def operatorShape {K : Type} (z : K) (add mul : K → K → K)
    (pow : K → Nat → K) (alpha : K) (a : Fin 4 → K) (q : K) : K :=
  mul (add (add (add (add z (mul (pow alpha 0) (a 0)))
    (mul (pow alpha 3) (a 1))) (mul (pow alpha 2) (a 2)))
    (mul (pow alpha 1) (a 3))) q

theorem operatorShape_congr {K : Type} (z z' : K)
    (add add' mul mul' : K → K → K) (pow pow' : K → Nat → K)
    (hz : z=z') (ha : ∀ x y,add x y=add' x y)
    (hm : ∀ x y,mul x y=mul' x y) (hp : ∀ x n,pow x n=pow' x n)
    (alpha : K) (a : Fin 4 → K) (q : K) :
    operatorShape z add mul pow alpha a q=operatorShape z' add' mul' pow' alpha a q := by
  have hadd : add=add' := funext fun x => funext fun y => ha x y
  have hmul : mul=mul' := funext fun x => funext fun y => hm x y
  have hpow : pow=pow' := funext fun x => funext fun n => hp x n
  rw [hz,hadd,hmul,hpow]

theorem field_operatorShape {K : Type} [Field K]
    (alpha : K) (a : Fin 4 → K) (q : K) :
    operatorShape (fieldZero : K) fieldAdd fieldMul fieldPow alpha a q=
      AspisR1S9SymbolicRowTransportV1.shape alpha a q := by rfl

private theorem source_operatorShape (alpha : E) (a : Nat → Q) :
    AspisR1S9ScalarConstructorModelV1.factorPolynomial alpha a=
      operatorShape (0 : E) (fun x y => x+y) concreteMul (fun x n => x^n)
        alpha (fun t : Fin 4 => AspisR1S9SharedScalarModelValuesV1.embedQ (a t.val))
        AspisR1S9ScalarActualPowerPolynomialV1.quarter := by rfl

/-- The SAME concrete factor polynomial is transported to the generic Field
shape through one proved operator bridge at a time, on opaque operands. -/
theorem source_factor_eq_generic_shape (alpha : E) (a : Nat → Q) :
    AspisR1S9ScalarConstructorModelV1.factorPolynomial alpha a=
      AspisR1S9SymbolicRowTransportV1.shape alpha
        (fun t : Fin 4 => AspisR1S9SharedScalarModelValuesV1.embedQ (a t.val))
        AspisR1S9ScalarActualPowerPolynomialV1.quarter := by
  have h := operatorShape_congr (0 : E) (fieldZero : E)
    (fun x y : E => x+y) fieldAdd concreteMul fieldMul
    (fun (x : E) (n : Nat) => x^n) fieldPow
    zero_operator_eq add_operator_eq mul_operator_eq pow_operator_eq
    alpha (fun t : Fin 4 => AspisR1S9SharedScalarModelValuesV1.embedQ (a t.val))
    AspisR1S9ScalarActualPowerPolynomialV1.quarter
  exact (source_operatorShape alpha a).trans (h.trans (field_operatorShape _ _ _))

#print axioms operatorShape_congr
#print axioms field_operatorShape
#print axioms source_factor_eq_generic_shape
end AspisR1S9SourceFactorShapeTransportV1

import S9WideFieldOperatorBridgesV1
import S9SymbolicRowTransportV1
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
namespace AspisR1S9SourceFactorShapeTransportV1
open AspisR1S9WideMulOperatorBridgeV1 (concreteMul fieldMul mul_operator_eq)
open AspisR1S9WideFieldOperatorBridgesV1
abbrev E := AspisWideTower.WideExact
abbrev Q := AspisR1S9SharedScalarModelValuesV1.ExactQM

def operatorFour {K : Type} (z : K) (add mul : K → K → K)
    (pow : K → Nat → K) (alpha a0 a1 a2 a3 q : K) : K :=
  mul (add (add (add (add z (mul (pow alpha 0) a0))
    (mul (pow alpha 3) a1)) (mul (pow alpha 2) a2)) (mul (pow alpha 1) a3)) q

theorem operatorFour_operators {K : Type} (z z' : K)
    (add add' mul mul' : K → K → K) (pow pow' : K → Nat → K)
    (hz : z=z') (ha : ∀ x y,add x y=add' x y)
    (hm : ∀ x y,mul x y=mul' x y) (hp : ∀ x n,pow x n=pow' x n)
    (alpha a0 a1 a2 a3 q : K) :
    operatorFour z add mul pow alpha a0 a1 a2 a3 q=
      operatorFour z' add' mul' pow' alpha a0 a1 a2 a3 q := by
  have hadd : add=add' := funext fun x => funext fun y => ha x y
  have hmul : mul=mul' := funext fun x => funext fun y => hm x y
  have hpow : pow=pow' := funext fun x => funext fun n => hp x n
  rw [hz,hadd,hmul,hpow]

theorem operatorFour_coefficients {K : Type} (z : K) (add mul : K → K → K)
    (pow : K → Nat → K) (alpha q a0 a1 a2 a3 b0 b1 b2 b3 : K)
    (h0 : a0=b0) (h1 : a1=b1) (h2 : a2=b2) (h3 : a3=b3) :
    operatorFour z add mul pow alpha a0 a1 a2 a3 q=
      operatorFour z add mul pow alpha b0 b1 b2 b3 q := by
  cases h0; cases h1; cases h2; cases h3; rfl

theorem field_operatorFour {K : Type} [Field K]
    (alpha : K) (a : Fin 4 → K) (q : K) :
    operatorFour (fieldZero : K) fieldAdd fieldMul fieldPow alpha (a 0) (a 1) (a 2) (a 3) q=
      AspisR1S9SymbolicRowTransportV1.shape alpha a q := by rfl

private theorem source_operatorFour (alpha : E) (a : Nat → Q) :
    AspisR1S9ScalarConstructorModelV1.factorPolynomial alpha a=
      operatorFour (0 : E) (fun x y => x+y) concreteMul (fun x n => x^n) alpha
        (AspisR1S9SharedScalarModelValuesV1.embedQ (a 0))
        (AspisR1S9SharedScalarModelValuesV1.embedQ (a 1))
        (AspisR1S9SharedScalarModelValuesV1.embedQ (a 2))
        (AspisR1S9SharedScalarModelValuesV1.embedQ (a 3))
        AspisR1S9ScalarActualPowerPolynomialV1.quarter := by rfl

/-- Transport operator paths and the FOUR small coefficient indices separately.
Fin's existing value lemma handles arbitrary opaque NeZero evidence before
any concrete field expression is compared. -/
theorem source_factor_eq_generic_shape (alpha : E) (a : Nat → Q) :
    AspisR1S9ScalarConstructorModelV1.factorPolynomial alpha a=
      AspisR1S9SymbolicRowTransportV1.shape alpha
        (fun t : Fin 4 => AspisR1S9SharedScalarModelValuesV1.embedQ (a t.val))
        AspisR1S9ScalarActualPowerPolynomialV1.quarter := by
  let g : Nat → E := fun i => AspisR1S9SharedScalarModelValuesV1.embedQ (a i)
  let af : Fin 4 → E := fun t => g t.val
  have v0 : (0 : Fin 4).val=0 := Fin.coe_ofNat_eq_mod 4 0
  have v1 : (1 : Fin 4).val=1 := Fin.coe_ofNat_eq_mod 4 1
  have v2 : (2 : Fin 4).val=2 := Fin.coe_ofNat_eq_mod 4 2
  have v3 : (3 : Fin 4).val=3 := Fin.coe_ofNat_eq_mod 4 3
  have c0 : g 0=af 0 := congrArg g v0.symm
  have c1 : g 1=af 1 := congrArg g v1.symm
  have c2 : g 2=af 2 := congrArg g v2.symm
  have c3 : g 3=af 3 := congrArg g v3.symm
  have hops := operatorFour_operators (0 : E) (fieldZero : E)
    (fun x y : E => x+y) fieldAdd concreteMul fieldMul
    (fun (x : E) (n : Nat) => x^n) fieldPow
    zero_operator_eq add_operator_eq mul_operator_eq pow_operator_eq
    alpha (g 0) (g 1) (g 2) (g 3) AspisR1S9ScalarActualPowerPolynomialV1.quarter
  have hcoeff := operatorFour_coefficients (fieldZero : E) fieldAdd fieldMul fieldPow
    alpha AspisR1S9ScalarActualPowerPolynomialV1.quarter
    (g 0) (g 1) (g 2) (g 3) (af 0) (af 1) (af 2) (af 3) c0 c1 c2 c3
  exact (source_operatorFour alpha a).trans
    (hops.trans (hcoeff.trans (field_operatorFour alpha af _)))

#print axioms operatorFour_operators
#print axioms operatorFour_coefficients
#print axioms field_operatorFour
#print axioms source_factor_eq_generic_shape
end AspisR1S9SourceFactorShapeTransportV1

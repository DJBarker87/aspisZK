import Wide.FinalEncoder
import AspisFormal.V6Width29CorrelatedAgreement
import AspisFormal.V5FriDegreeThreeCorrelatedAgreement

/-! Linear closure and scalar-power curves, copied from
`K1/V7ExactCorrelatedAgreement.lean` before its interpolation section. -/
set_option autoImplicit false
namespace AspisWide.Agreement
open scoped BigOperators
open Polynomial
open AspisWide.InitialEncoder AspisWide.FinalEncoder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6Width29CorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
noncomputable section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]

private theorem naturalCoefficientPolynomial_eval_add
    {n : Nat} (positive : 0 < n) (left right : Fin n → E)
    (x : E) :
    (naturalCoefficientPolynomial (left + right)).eval x =
      (naturalCoefficientPolynomial left).eval x +
        (naturalCoefficientPolynomial right).eval x := by
  rw [naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem naturalCoefficientPolynomial_eval_smul
    {n : Nat} (positive : 0 < n) (scalar : E)
    (coefficients : Fin n → E) (x : E) :
    (naturalCoefficientPolynomial (scalar • coefficients)).eval x =
      scalar * (naturalCoefficientPolynomial coefficients).eval x := by
  rw [naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem initialP0_eval_add
    (left right : InitialMessage E) (x : E) :
    (initialP0 (left + right)).eval x =
      (initialP0 left).eval x + (initialP0 right).eval x := by
  unfold initialP0
  have coordinates :
      evenCoefficients (n := 512) (left + right) =
        evenCoefficients (n := 512) left +
          evenCoefficients (n := 512) right := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_add (by norm_num) _ _ x

private theorem initialP1_eval_add
    (left right : InitialMessage E) (x : E) :
    (initialP1 (left + right)).eval x =
      (initialP1 left).eval x + (initialP1 right).eval x := by
  unfold initialP1
  have coordinates :
      oddCoefficients (n := 512) (left + right) =
        oddCoefficients (n := 512) left +
          oddCoefficients (n := 512) right := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_add (by norm_num) _ _ x

private theorem initialP0_eval_smul
    (scalar : E) (message : InitialMessage E)
    (x : E) :
    (initialP0 (scalar • message)).eval x =
      scalar * (initialP0 message).eval x := by
  unfold initialP0
  have coordinates :
      evenCoefficients (n := 512) (scalar • message) =
        scalar • evenCoefficients (n := 512) message := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_smul (by norm_num) scalar _ x

private theorem initialP1_eval_smul
    (scalar : E) (message : InitialMessage E)
    (x : E) :
    (initialP1 (scalar • message)).eval x =
      scalar * (initialP1 message).eval x := by
  unfold initialP1
  have coordinates :
      oddCoefficients (n := 512) (scalar • message) =
        scalar • oddCoefficients (n := 512) message := by
    funext coefficient
    rfl
  rw [coordinates]
  exact naturalCoefficientPolynomial_eval_smul (by norm_num) scalar _ x

/-- The exact released initial circle encoder, packaged as a QM31-linear map.
This proves closure of the actual 1024-coordinate message image, not of the
larger ambient degree-at-most-1024 polynomial space. -/
noncomputable def exactInitialLinear :
    InitialMessage E →ₗ[E] InitialWord E where
  toFun := exactInitialEncoder
  map_add' := by
    intro left right
    funext index
    simp only [exactInitialEncoder]
    rw [initialP0_eval_add, initialP1_eval_add]
    simp only [Pi.add_apply, exactInitialEncoder]
    ring
  map_smul' := by
    intro scalar message
    funext index
    simp only [exactInitialEncoder]
    rw [initialP0_eval_smul, initialP1_eval_smul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      exactInitialEncoder]
    ring

@[simp] theorem exactInitialLinear_apply
    (message : InitialMessage E) :
    exactInitialLinear message = exactInitialEncoder message := rfl

theorem exactInitialEncoder_add
    (left right : InitialMessage E) :
    exactInitialEncoder (left + right) =
      exactInitialEncoder left + exactInitialEncoder right :=
  exactInitialLinear.map_add left right

theorem exactInitialEncoder_smul
    (scalar : E) (message : InitialMessage E) :
    exactInitialEncoder (scalar • message) =
      scalar • exactInitialEncoder message :=
  exactInitialLinear.map_smul scalar message

/-- The final released line encoder already is the existing exact linear map. -/
theorem exactFinalEncoder_add
    (left right : FinalMessage E) :
    exactFinalEncoder (left + right) =
      exactFinalEncoder left + exactFinalEncoder right :=
  exactFinalLinear.map_add left right

theorem exactFinalEncoder_smul
    (scalar : E) (message : FinalMessage E) :
    exactFinalEncoder (scalar • message) =
      scalar • exactFinalEncoder message :=
  exactFinalLinear.map_smul scalar message

/-! ## Scalar-power curves remain in the exact released images -/

/-- The actual initial message on the scalar-power curve.  This is a message
of the released `Fin 1024 -> E` type, not an ambient GRS polynomial. -/
def exactInitialMessageCurve
    (components : Fin 29 → InitialMessage E) (gamma : E) :
    InitialMessage E :=
  ∑ lane, gamma ^ lane.1 • components lane

/-- The actual final message on the degree-three scalar-power curve. -/
def exactFinalMessageCurve
    (components : Fin 4 → FinalMessage E) (z : E) :
    FinalMessage E :=
  ∑ lane, z ^ lane.1 • components lane

@[simp] theorem exactInitialMessageCurve_apply
    (components : Fin 29 → InitialMessage E) (gamma : E)
    (coefficient : Fin 1024) :
    exactInitialMessageCurve components gamma coefficient =
      width29Batch (fun lane => components lane coefficient) gamma := by
  simp only [exactInitialMessageCurve, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, width29Batch]
  apply Finset.sum_congr rfl
  intro lane _
  ring

@[simp] theorem exactFinalMessageCurve_apply
    (components : Fin 4 → FinalMessage E) (z : E)
    (coefficient : Fin 256) :
    exactFinalMessageCurve components z coefficient =
      AspisV5FunctionalBatching.batchedDiscrepancy
        (fun lane => components lane coefficient) z := by
  rw [exactFinalMessageCurve, Finset.sum_apply, Fin.sum_univ_four]
  simp only [Pi.smul_apply, smul_eq_mul,
    AspisV5FunctionalBatching.batchedDiscrepancy]
  norm_num
  ring

/-- Exact initial closure: encoding the released message curve is pointwise
the width-29 curve through the encoded released component messages. -/
theorem exactInitialEncoder_messageCurve
    (components : Fin 29 → InitialMessage E) (gamma : E) :
    exactInitialEncoder (exactInitialMessageCurve components gamma) =
      fun index => width29CurveValue
        (fun lane => exactInitialEncoder (components lane)) gamma index := by
  change exactInitialLinear (exactInitialMessageCurve components gamma) = _
  rw [exactInitialMessageCurve, map_sum]
  simp_rw [map_smul]
  funext index
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    width29CurveValue, width29Batch,
    exactInitialLinear_apply]
  apply Finset.sum_congr rfl
  intro lane _
  ring

/-- Exact final closure for the released degree-three message curve. -/
theorem exactFinalEncoder_messageCurve
    (components : Fin 4 → FinalMessage E) (z : E) :
    exactFinalEncoder (exactFinalMessageCurve components z) =
      fun index => curveValue
        (fun lane => exactFinalEncoder (components lane)) z index := by
  change exactFinalLinear (exactFinalMessageCurve components z) = _
  rw [exactFinalMessageCurve, map_sum]
  simp_rw [map_smul]
  funext index
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    curveValue,
    AspisV5FunctionalBatching.batchedDiscrepancy, Fin.sum_univ_four,
    exactFinalEncoder]
  norm_num
  ring

theorem exactInitialEncoder_injective :
    Function.Injective (exactInitialEncoder (K := E)) := by
  intro left right codeEqual
  by_contra different
  have cap := exactInitialEncoder_overlap_cap left right different
  rw [codeEqual] at cap
  simp [agreementCount] at cap

#print axioms exactInitialEncoder_injective
#print axioms exactInitialLinear
#print axioms exactInitialEncoder_messageCurve
#print axioms exactFinalEncoder_messageCurve
end
end AspisWide.Agreement

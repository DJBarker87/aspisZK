import Wide.InitialEncoder

/-! The exact initial encoder commutes with every field conjugation: its
natural-basis factors and stored coordinates are defined over the prime field. -/
set_option autoImplicit false
namespace AspisWide.EncoderConjugation
open AspisCircleTensorBinding
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem map_doubledFactor (σ : K →+* K) (x : K) (n : Nat) :
    σ (doubledFactor x n) = doubledFactor (σ x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [doubledFactor, map_sub, map_mul, map_pow, map_ofNat, map_one, ih]

theorem map_naturalLineValue (σ : K →+* K) (x : K) (n : Nat) :
    σ (naturalLineValue x n) = naturalLineValue (σ x) n := by
  simp only [naturalLineValue, map_prod, map_doubledFactor]

theorem map_naturalCoefficientPolynomial_eval (σ : K →+* K)
    {n : Nat} (positive : 0 < n) (coefficients : Fin n → K) (x : K) :
    σ ((naturalCoefficientPolynomial coefficients).eval x) =
      (naturalCoefficientPolynomial (fun i => σ (coefficients i))).eval (σ x) := by
  rw [naturalCoefficientPolynomial_eval_eq_sum positive,
    naturalCoefficientPolynomial_eval_eq_sum positive]
  simp only [map_sum, map_mul, map_naturalLineValue]

theorem map_primeField (σ : K →+* K) (x : ZMod AspisCircleGroupOrder.P) :
    σ (algebraMap (ZMod AspisCircleGroupOrder.P) K x) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K x := by
  have unique : σ.comp (algebraMap (ZMod AspisCircleGroupOrder.P) K) =
      algebraMap (ZMod AspisCircleGroupOrder.P) K := Subsingleton.elim _ _
  exact DFunLike.congr_fun unique x

theorem map_initialEncoder (σ : K →+* K) (message : InitialMessage K) :
    exactInitialEncoder (fun i => σ (message i)) =
      fun x => σ (exactInitialEncoder message x) := by
  funext x
  simp only [exactInitialEncoder, map_add, map_mul, initialP0, initialP1,
    map_naturalCoefficientPolynomial_eval σ (by norm_num : 0 < 512), map_primeField]
  rfl

#print axioms map_doubledFactor
#print axioms map_naturalLineValue
#print axioms map_naturalCoefficientPolynomial_eval
#print axioms map_primeField
#print axioms map_initialEncoder
end AspisWide.EncoderConjugation

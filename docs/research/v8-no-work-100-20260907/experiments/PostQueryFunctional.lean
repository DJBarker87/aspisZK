import OptimizedRelationRefinement
import ImageCallbackInterfaces
import AspisFormal.V7ExactOneFoldDomains

/-! The actual post-query natural-line functional, retaining query order.
These are deterministic field/source-shaped interfaces, not a ROM law or a
proof that an arbitrary committed word has polynomial coefficients. A reference
Q is explicit. The received folded word remains an arbitrary function. -/
set_option autoImplicit false
namespace AspisV8.PostQueryFunctional
open Polynomial
open AspisCircleTensorBinding AspisV5FriConcreteEncoderApplicability
open AspisV5FriRelationCandidateBridge AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation AspisV5FriInitialCircleEncoderIdentity
open AspisV8.JointImageGame AspisV8.OptimizedRelationRefinement
universe u
variable {K : Type u} [Field K] [DecidableEq K] [NeZero (2 : K)]

def lineWeight (x : K) (i : Fin 256) : K := naturalLineValue x i.val
noncomputable def lineEval (v : Fin 256 → K) (x : K) : K :=
  (naturalCoefficientPolynomial v).eval x

theorem lineEval_dot (v : Fin 256 → K) (x : K) :
    lineEval v x = candidateClaim (lineWeight x) v :=
  naturalCoefficientPolynomial_eval_eq_sum (by norm_num) v x

noncomputable def lineEvaluationLinear (x : K) : (Fin 256 → K) →ₗ[K] K where
  toFun := fun v => lineEval v x
  map_add' f g := by
    simp [lineEval_dot, candidateClaim, add_mul, Finset.sum_add_distrib]
  map_smul' a f := by
    simp [lineEval_dot, candidateClaim, Finset.mul_sum, mul_assoc]

theorem lineEval_coefficient_fold (Q : Fin 1024 → K) (a x : K) :
    lineEval (coefficientFoldLayer 256 a Q) x =
      coefficientFoldValue a (fun lane => lineEval (coefficientLane 256 lane Q) x) := by
  change lineEvaluationLinear x (coefficientFoldLayer 256 a Q) = _
  rw [coefficientFoldLayer_eq_lane_combination]
  simp only [map_add, map_smul, smul_eq_mul, coefficientFoldValue]
  rfl

/-- The literal natural circle polynomial from the even/odd coefficient
halves, with the source's (x,y),(x,-y),(-x,-y),(-x,y) slot order. -/
noncomputable def circleValue (Q : Fin 1024 → K) (x y : K) : K :=
  (initialP0 Q).eval x+y*(initialP1 Q).eval x
noncomputable def circleFibre (Q : Fin 1024 → K) (x y : K) : Fin 4 → K :=
  ![circleValue Q x y,circleValue Q x (-y),circleValue Q (-x) (-y),circleValue Q (-x) y]

theorem circleFibre_radix4 (Q : Fin 1024 → K) (x y : K) :
    circleFibre Q x y = radix4Evaluate y (-y) x
      (fun lane => lineEval (coefficientLane 256 lane Q) (doubledFactor x 1)) := by
  funext slot
  fin_cases slot <;>
    simp [circleFibre, circleValue, initialP0_eval_lanes, initialP1_eval_lanes,
      radix4Evaluate, lineEval, doubledFactor] <;> ring

/-- Actual normalized four-slot fold for a polynomial input. Inverses are
constructed from nonzero coordinates, not supplied with an unproved equality.
This never asserts that an arbitrary received quotient is this polynomial. -/
theorem circleFibre_fold (Q : Fin 1024 → K) (a x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    circleFoldValue a (2*x)⁻¹ (2*y)⁻¹ (circleFibre Q x y) =
      lineEval (coefficientFoldLayer 256 a Q) (2*x^2-1) := by
  rw [circleFibre_radix4, circleFoldValue_radix4Evaluate a x y]
  · exact (lineEval_coefficient_fold Q a (doubledFactor x 1)).symm
  · exact mul_inv_cancel₀ (mul_ne_zero (NeZero.ne (2 : K)) hx)
  · exact mul_inv_cancel₀ (mul_ne_zero (NeZero.ne (2 : K)) hy)

/-- The reference vector is an analysis object, not a witness-side argument
to the byte verifier. No assertion about its relation to a received word is
part of this structure. The final vector is supplied only after alpha0. -/
structure Prefix where
  ordinary : Fin 1024 → K
  referenceQ : Fin 1024 → K
  claim : K
  quarter : K
  tau : K
  b : K
  c : K
  alpha0 : K
  response0 : Sent K

def Prefix.imageWeight (p : Prefix (K := K)) : Fin 1024 → K :=
  ImageCallbackInterfaces.imageWeights p.ordinary
    ⟨1023, by decide⟩ ⟨1022, by decide⟩ ⟨1021, by decide⟩ p.tau p.b p.c
def Prefix.foldWeight (p : Prefix (K := K)) : Fin 256 → K :=
  dualWeightFoldLayer 256 p.alpha0 p.imageWeight
def Prefix.referenceFinal (p : Prefix (K := K)) : Fin 256 → K :=
  coefficientFoldLayer 256 p.alpha0 p.referenceQ
def Prefix.carried (p : Prefix (K := K)) : K :=
  nextClaim p.quarter p.claim p.response0 p.alpha0
noncomputable def Prefix.trueError (p : Prefix (K := K)) : K :=
  (discrepancy 256 p.quarter p.claim p.response0 p.imageWeight p.referenceQ).eval p.alpha0
def Prefix.prior (p : Prefix (K := K)) (final : Fin 256 → K) : K :=
  p.carried-candidateClaim p.foldWeight final
noncomputable def Prefix.difference (p : Prefix (K := K)) (final : Fin 256 → K) : K[X] :=
  naturalCoefficientPolynomial final-naturalCoefficientPolynomial p.referenceFinal

theorem difference_degree (p : Prefix (K := K)) (final : Fin 256 → K) :
    (p.difference final).natDegree ≤ 255 := by
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  exact max_le (naturalCoefficientPolynomial_natDegree_le (by norm_num) final)
    (naturalCoefficientPolynomial_natDegree_le (by norm_num) p.referenceFinal)

/-- Prove the symbolic identity before substituting a concrete folded vector;
this avoids normalizing a 256-entry fold during rewriting. -/
theorem natural_difference_zero_iff {n : Nat} (f g : Fin n → K) :
    naturalCoefficientPolynomial f-naturalCoefficientPolynomial g=0 ↔ f=g := by
  rw [sub_eq_zero]
  exact (naturalCoefficientPolynomial_injective (K := K)).eq_iff

/-- Natural-basis injectivity derives coefficient equality from the game's
zero polynomial. It is not supplied as a target-identity premise. -/
theorem difference_zero_iff (p : Prefix (K := K)) (final : Fin 256 → K) :
    p.difference final=0 ↔ final=p.referenceFinal := by
  unfold Prefix.difference
  exact natural_difference_zero_iff final p.referenceFinal

theorem same_prior (p : Prefix (K := K)) (final : Fin 256 → K)
    (same : p.difference final=0) : p.prior final=p.trueError := by
  rw [(difference_zero_iff p final).mp same]
  exact (discrepancy_eval 256 p.quarter p.claim p.response0
    p.imageWeight p.referenceQ p.alpha0).symm

/-- Query order is part of the input: ordinal j has scale rho^(j+1).
Sorting the authentication frontier never sorts this array. -/
def postWeights {q : Nat} (p : Prefix (K := K)) (points : Fin q → K) (rho : K) :
    Fin 256 → K := fun i =>
  p.foldWeight i + ∑ j, rho^(j.val+1)*lineWeight (points j) i
def increment {q : Nat} (points : Fin q → K) (received : K → K) (rho : K) : K :=
  ∑ j, rho^(j.val+1)*received (points j)
def postClaim {q : Nat} (p : Prefix (K := K)) (points : Fin q → K)
    (received : K → K) (rho : K) : K := p.carried+increment points received rho
noncomputable def residual {q : Nat} (final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) : Fin q → K :=
  fun j => lineEval final (points j)-received (points j)
noncomputable def noise (p : Prefix (K := K)) (received : K → K) (x : K) : K :=
  received x-lineEval p.referenceFinal x

/-- Reuses the proved generic injection, instantiating the actual natural
line basis and PLUS updates to scalar and covector. No zero residual, correct
prior, source polynomiality, or target membership is assumed. -/
theorem post_discrepancy {q : Nat} (p : Prefix (K := K)) (final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) (rho : K) :
    postClaim p points received rho-candidateClaim (postWeights p points rho) final =
      (shifted (p.prior final) (residual final points received)).eval rho := by
  have h := ImageCallbackInterfaces.query_injection 256 q final p.foldWeight
    (fun j => lineWeight (points j)) (fun j => received (points j)) p.carried rho
  have hd : ∀ j : Fin q, (∑ i, final i*lineWeight (points j) i)=lineEval final (points j) := by
    intro j
    exact (lineEval_dot final (points j)).symm
  simp_rw [hd] at h
  simpa only [postClaim, increment, postWeights, candidateClaim, Prefix.prior,
    shifted, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, monomialPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, residual] using h

/-- For arbitrary received data, the noise records its actual difference
from the reference fold. It is not declared zero or supported on a small set. -/
theorem natural_residual_zero_iff {q : Nat} (reference final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) :
    residual final points received=0 ↔
      ∀ j, (naturalCoefficientPolynomial final-naturalCoefficientPolynomial reference).eval
        (points j)=received (points j)-lineEval reference (points j) := by
  simp only [funext_iff, residual, Pi.zero_apply, sub_eq_zero,
    Polynomial.eval_sub, lineEval, sub_left_inj]

theorem residual_zero_iff {q : Nat} (p : Prefix (K := K)) (final : Fin 256 → K)
    (points : Fin q → K) (received : K → K) :
    residual final points received=0 ↔
      ∀ j, (p.difference final).eval (points j)=noise p received (points j) := by
  unfold Prefix.difference noise
  exact natural_residual_zero_iff p.referenceFinal final points received

theorem residual_zero_iff_on_image {q : Nat} (p : Prefix (K := K))
    (final : Fin 256 → K) (points : Fin q → K) (received : K → K) :
    residual final points received=0 ↔
      ∀ x ∈ Finset.univ.image points, (p.difference final).eval x=noise p received x := by
  rw [residual_zero_iff]
  constructor
  · intro h x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact h j
  · intro h j
    exact h (points j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

/-- Exact-polynomial specialization; the caller must actually establish the
received word is this evaluation function to apply it to quotient openings. -/
theorem exact_residual_zero_iff {q : Nat} (p : Prefix (K := K))
    (final : Fin 256 → K) (points : Fin q → K) :
    residual final points (lineEval p.referenceFinal)=0 ↔
      ∀ j, (p.difference final).eval (points j)=0 := by
  simpa only [noise, sub_self] using
    residual_zero_iff p final points (lineEval p.referenceFinal)

/-- Complete causal compact suffix with the initial discrepancy now DERIVED
from the actual post-query functional. A caller may choose raw after seeing
the ordered schedule and rho; raw itself enforces later causal responses. -/
noncomputable def tail {q : Nat} (p : Prefix (K := K)) (hq : p.quarter*4=1)
    (final : Fin 256 → K) (points : Fin q → K) (received : K → K) (rho : K)
    (raw : RawRounds (K := K) 3 256) :
    Rounds 3 ((shifted (p.prior final) (residual final points received)).eval rho) :=
  post_discrepancy p final points received rho ▸
    raw.toGame p.quarter hq (postWeights p points rho) final (postClaim p points received rho)

theorem tail_acceptance_iff {q : Nat} (p : Prefix (K := K)) (hq : p.quarter*4=1)
    (final : Fin 256 → K) (points : Fin q → K) (received : K → K) (rho : K)
    (raw : RawRounds (K := K) 3 256) (alphas : List K) :
    raw.accepts p.quarter (postWeights p points rho) final (postClaim p points received rho) alphas ↔
      terminalZero (tail p hq final points received rho raw) alphas := by
  simpa only [tail, terminalZero_transport] using
    raw_acceptance_iff_terminal_zero p.quarter hq raw (postWeights p points rho)
      final (postClaim p points received rho) alphas

section ExactStoredDomain
variable [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Exact log18 stored coordinate reused from V7, with its original
bit-reversal ordering, not a natural-order domain substituted by cardinality. -/
def storedPoint (i : Fin 262144) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 i)

theorem storedPoint_injective : Function.Injective (storedPoint (K := K)) := by
  intro i j h
  apply AspisV7ExactOneFoldDomains.storedFirstLineX18_injective
  exact FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K h

theorem storedPoint_source_pi (i : Fin 262144) :
    storedPoint (K := K) i =
      2*(algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisCircleGroupOrder.X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 i)))^2-1 := by
  simpa only [storedPoint, doubledFactor] using
    AspisV7ExactOneFoldDomains.storedFirstLineX18_eq_doubled_algebraMap (K := K) i

theorem ordered_stored_points_distinct {q : Nat} (queries : Fin q ↪ Fin 262144) :
    Function.Injective (fun j => storedPoint (K := K) (queries j)) :=
  storedPoint_injective.comp queries.injective
end ExactStoredDomain

#print axioms lineEval_dot
#print axioms lineEval_coefficient_fold
#print axioms circleFibre_radix4
#print axioms circleFibre_fold
#print axioms difference_degree
#print axioms difference_zero_iff
#print axioms same_prior
#print axioms post_discrepancy
#print axioms residual_zero_iff
#print axioms residual_zero_iff_on_image
#print axioms exact_residual_zero_iff
#print axioms tail
#print axioms tail_acceptance_iff
#print axioms storedPoint_injective
#print axioms storedPoint_source_pi
#print axioms ordered_stored_points_distinct
end AspisV8.PostQueryFunctional

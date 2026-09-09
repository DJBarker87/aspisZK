import AspisFormal.V5FriConcreteEncoderApplicability
import Mathlib.LinearAlgebra.Lagrange

/-! Research only. Four globally code-valued folds force an arbitrary fixed
received word into the full circle-lift code. The final coefficient vector
may depend on alpha. No provider success, exact received polynomiality or
membership in the original/image-constrained code is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.ExactFoldRecovery
open Polynomial Finset
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability

noncomputable section
variable {K Pos : Type*} [Field K] [DecidableEq K]

/-- Interpolation takes place in the code submodule. The four evaluation
words, not four post-hoc coefficient targets, determine all coefficients. -/
theorem four_code_evaluations_recover_coefficients
    (C : Submodule K (Pos → K)) (v : Pos → K[X]) (nodes : Finset K)
    (four : nodes.card = 4) (degree : ∀ i, (v i).natDegree ≤ 3)
    (inside : ∀ a ∈ nodes, (fun i => (v i).eval a) ∈ C) (j : Nat) :
    (fun i => (v i).coeff j) ∈ C := by
  classical
  have equal (i : Pos) :
      v i = Lagrange.interpolate nodes id (fun a => (v i).eval a) := by
    apply Lagrange.eq_interpolate_of_eval_eq
      _ (fun _ _ _ _ h => h) _ (fun _ _ => rfl)
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    apply WithBot.coe_lt_coe.mpr
    rw [four]
    exact Nat.lt_succ_of_le (degree i)
  have coefficient : (fun i => (v i).coeff j) =
      ∑ a ∈ nodes, (Lagrange.basis nodes id a).coeff j • (fun i => (v i).eval a) := by
    funext i
    rw [equal i]
    simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, coeff_C_mul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [coefficient]
  exact C.sum_mem fun a ha => C.smul_mem _ (inside a ha)

variable {F : Type*} [Field F] [Algebra F K]

def decodedSlots {m : Nat} (inverse2x inverse2y : Fin m → F)
    (received : Fin (4*m) → K) (i : Fin m) : Fin 4 → K :=
  radix4Decode (algebraMap F K (inverse2y i))
    (-(algebraMap F K (inverse2y i))) (algebraMap F K (inverse2x i))
    (fun slot => received (childIndex i slot))

def foldCurve {m : Nat} (inverse2x inverse2y : Fin m → F)
    (received : Fin (4*m) → K) (i : Fin m) : K[X] :=
  monomialPolynomial (decodedSlots inverse2x inverse2y received i)

theorem foldCurve_degree {m : Nat} (inverse2x inverse2y : Fin m → F)
    (received : Fin (4*m) → K) (i : Fin m) :
    (foldCurve inverse2x inverse2y received i).natDegree ≤ 3 :=
  monomialPolynomial_natDegree_le (by decide) _

theorem foldCurve_eval_actual {m : Nat} (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (alpha : K) (i : Fin m) :
    (foldCurve inverse2x inverse2y received i).eval alpha =
      circleFoldLayer m alpha inverse2x inverse2y received i := by
  rw [circleFoldLayer_apply,
    circleFoldValue_eq_coefficientFoldValue_decode alpha (x i) (y i)
      (algebraMap F K (inverse2x i)) (algebraMap F K (inverse2y i)) (hx i) (hy i)]
  simp only [foldCurve, monomialPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Fin.sum_univ_four, decodedSlots, coefficientFoldValue]
  have zero : ((0 : Fin 4) : Nat) = 0 := rfl
  have one : ((1 : Fin 4) : Nat) = 1 := rfl
  have two : ((2 : Fin 4) : Nat) = 2 := rfl
  have three : ((3 : Fin 4) : Nat) = 3 := rfl
  rw [zero, one, two, three]
  ring

/-- The actual normalized four-slot inverse reconstructs the received word
from four final-code coefficient words, not from a supplied anchor. -/
theorem decoded_slots_in_range_reconstruct {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K)
    (inside : ∀ slot : Fin 4,
      (fun i => decodedSlots inverse2x inverse2y received i slot) ∈ LinearMap.range encoder) :
    received ∈ LinearMap.range (circleLiftEncoder encoder x y) := by
  classical
  choose messages exactMessages using inside
  let message : Fin (4*n) → K := fun index => messages (slotIndex index) (parentIndex index)
  have lanes (slot : Fin 4) : coefficientLane n slot message = messages slot := by
    funext i
    simp only [coefficientLane_apply, message, slotIndex_childIndex, parentIndex_childIndex]
  refine ⟨message, ?_⟩
  funext index
  let i := parentIndex index
  let s := slotIndex index
  have atChild : circleLiftEncoder encoder x y message (childIndex i s) =
      received (childIndex i s) := by
    rw [circleLiftEncoder, radix4LiftEncoder_apply_child]
    have decoded : (fun lane => encoder (coefficientLane n lane message) i) =
        decodedSlots inverse2x inverse2y received i := by
      funext lane
      rw [lanes lane]
      exact congrFun (exactMessages lane) i
    rw [decoded]
    have inverse := radix4Evaluate_radix4Decode (y i) (-y i) (x i)
      (algebraMap F K (inverse2y i)) (-(algebraMap F K (inverse2y i)))
      (algebraMap F K (inverse2x i)) (hy i)
      (by simpa only [neg_mul, mul_neg, neg_neg] using hy i) (hx i)
      (fun slot => received (childIndex i slot))
    exact congrFun inverse s
  simpa only [i, s, childIndex_parentIndex_slotIndex] using atChild

def exactFoldChallenges {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (inverse2x inverse2y : Fin m → F) (received : Fin (4*m) → K)
    (challenges : Finset K) : Finset K := by
  classical
  exact challenges.filter fun alpha =>
    circleFoldLayer m alpha inverse2x inverse2y received ∈ LinearMap.range encoder

/-- If four distinct alpha values yield some globally matching final code
word, received itself belongs to the full circle-lift code. -/
theorem four_exact_folds_recover_received {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (challenges : Finset K)
    (many : 4 ≤ (exactFoldChallenges encoder inverse2x inverse2y received challenges).card) :
    received ∈ LinearMap.range (circleLiftEncoder encoder x y) := by
  classical
  obtain ⟨nodes, subset, four⟩ := Finset.exists_subset_card_eq many
  have inCode (a : K) (ha : a ∈ nodes) :
      (fun i => (foldCurve inverse2x inverse2y received i).eval a) ∈
        LinearMap.range encoder := by
    have member := (Finset.mem_filter.mp (subset ha)).2
    have equal : (fun i => (foldCurve inverse2x inverse2y received i).eval a) =
        circleFoldLayer m a inverse2x inverse2y received := by
      funext i
      exact foldCurve_eval_actual x y inverse2x inverse2y hx hy received a i
    rwa [equal]
  apply decoded_slots_in_range_reconstruct encoder x y inverse2x inverse2y hx hy received
  intro slot
  have coeff := four_code_evaluations_recover_coefficients (LinearMap.range encoder)
    (foldCurve inverse2x inverse2y received) nodes four
    (foldCurve_degree inverse2x inverse2y received) inCode slot.val
  simpa only [foldCurve, monomialPolynomial_coeff] using coeff

/-- Quantitative residual reduction for arbitrary non-code received words.
This is not a bound on partial agreement or all verifier acceptance. -/
theorem noncode_exact_fold_challenges_le_three {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (challenges : Finset K)
    (outside : received ∉ LinearMap.range (circleLiftEncoder encoder x y)) :
    (exactFoldChallenges encoder inverse2x inverse2y received challenges).card ≤ 3 := by
  by_contra notBound
  exact outside (four_exact_folds_recover_received encoder x y inverse2x inverse2y
    hx hy received challenges (by omega))

/-- The final message may be selected after alpha. Its exact matches are a
subset of the existential code-valued event already bounded above. -/
theorem adaptive_global_final_matches_le_three {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (challenges : Finset K)
    (outside : received ∉ LinearMap.range (circleLiftEncoder encoder x y))
    (final : K → Fin n → K) :
    (challenges.filter fun alpha => encoder (final alpha) =
      circleFoldLayer m alpha inverse2x inverse2y received).card ≤ 3 := by
  classical
  apply (Finset.card_le_card ?_).trans
    (noncode_exact_fold_challenges_le_three encoder x y inverse2x inverse2y hx hy
      received challenges outside)
  intro alpha member
  obtain ⟨ha, exactFinal⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨ha, ⟨final alpha, exactFinal⟩⟩

/-- A literal obstruction to reusing V7 raw-word QueryConsistent with the
same V8 final: raw U=1 has honest interpolant I=1 and quotient zero. The
quotient fold is zero while the raw fold is one, for every alpha. This is
an algebraic interface diagnostic, not a payment proof or forgery. -/
theorem raw_quotient_fold_separation [NeZero (2 : K)]
    (alpha inverse2x inverse2y denominator : K) :
    circleFoldValue alpha inverse2x inverse2y
        (fun _ => ((1 : K)-1)/denominator) = 0 ∧
      circleFoldValue alpha inverse2x inverse2y (fun _ => 1) = 1 := by
  constructor
  · simp [circleFoldValue, lineFoldValue, pairFoldValue]
  · simp [circleFoldValue, lineFoldValue, pairFoldValue]

#print axioms four_code_evaluations_recover_coefficients
#print axioms foldCurve_eval_actual
#print axioms decoded_slots_in_range_reconstruct
#print axioms four_exact_folds_recover_received
#print axioms noncode_exact_fold_challenges_le_three
#print axioms adaptive_global_final_matches_le_three
#print axioms raw_quotient_fold_separation
end
end AspisV8.ExactFoldRecovery

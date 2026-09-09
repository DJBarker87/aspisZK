import ExactFoldRecovery

/-! Research-only common-support recovery for arbitrary received words.
No anchor, exact received polynomiality, provider success or image validity
is assumed. This does not give a useful 100-bit q22 query bound by itself. -/

set_option autoImplicit false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.PartialFoldRecovery

open Polynomial Finset
open AspisV8.ExactFoldRecovery
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability

noncomputable section

variable {K F : Type*} [Field K] [DecidableEq K] [Field F] [Algebra F K]

/-- Four code-valued folds on a common support reconstruct all four original
slots on that support. Code linearity is restricted to S before interpolation;
the resulting coefficient messages still belong to the full global code. -/
theorem four_support_folds_recover {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (nodes : Finset K) (four : nodes.card=4)
    (final : K → Fin n → K) (support : Set (Fin m))
    (matched : ∀ a ∈ nodes, ∀ i ∈ support,
      encoder (final a) i = circleFoldLayer m a inverse2x inverse2y received i) :
    ∃ message : Fin (4*n) → K, ∀ i ∈ support, ∀ slot : Fin 4,
      circleLiftEncoder encoder x y message (childIndex i slot) =
        received (childIndex i slot) := by
  classical
  let restricted : (Fin n → K) →ₗ[K] (support → K) :=
    { toFun := fun message i => encoder message i.val
      map_add' := by
        intro a b
        funext i
        exact congrFun (encoder.map_add a b) i.val
      map_smul' := by
        intro a b
        funext i
        exact congrFun (encoder.map_smul a b) i.val }
  have inCode (a : K) (ha : a ∈ nodes) :
      (fun i : support => (foldCurve inverse2x inverse2y received i.val).eval a) ∈
        LinearMap.range restricted := by
    refine ⟨final a, ?_⟩
    funext i
    change encoder (final a) i.val =
      (foldCurve inverse2x inverse2y received i.val).eval a
    rw [foldCurve_eval_actual x y inverse2x inverse2y hx hy received a i.val]
    exact matched a ha i.val i.property
  have coefficients (slot : Fin 4) :
      (fun i : support => decodedSlots inverse2x inverse2y received i.val slot) ∈
        LinearMap.range restricted := by
    have h := four_code_evaluations_recover_coefficients (LinearMap.range restricted)
      (fun i : support => foldCurve inverse2x inverse2y received i.val) nodes four
      (fun i => foldCurve_degree inverse2x inverse2y received i.val) inCode slot.val
    simpa only [foldCurve, monomialPolynomial_coeff] using h
  choose messages exactMessages using coefficients
  let message : Fin (4*n) → K := fun index => messages (slotIndex index) (parentIndex index)
  have lanes (slot : Fin 4) : coefficientLane n slot message = messages slot := by
    funext i
    simp only [coefficientLane_apply, message, slotIndex_childIndex, parentIndex_childIndex]
  refine ⟨message, ?_⟩
  intro i hi slot
  rw [circleLiftEncoder, radix4LiftEncoder_apply_child]
  have decoded : (fun lane => encoder (coefficientLane n lane message) i) =
      decodedSlots inverse2x inverse2y received i := by
    funext lane
    rw [lanes lane]
    exact congrFun (exactMessages lane) ⟨i, hi⟩
  rw [decoded]
  have inverse := radix4Evaluate_radix4Decode (y i) (-y i) (x i)
    (algebraMap F K (inverse2y i)) (-(algebraMap F K (inverse2y i)))
    (algebraMap F K (inverse2x i)) (hy i)
    (by simpa only [neg_mul, mul_neg, neg_neg] using hy i) (hx i)
    (fun s => received (childIndex i s))
  exact congrFun inverse slot

def fibreBad {m : Nat} (left right : Fin (4*m) → K) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ∃ slot : Fin 4,
    left (childIndex i slot) ≠ right (childIndex i slot)

def foldedBad {n m : Nat} (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (inverse2x inverse2y : Fin m → F) (received : Fin (4*m) → K)
    (alpha : K) (final : Fin n → K) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i =>
    encoder final i ≠ circleFoldLayer m alpha inverse2x inverse2y received i

/-- The union bound is applied only after constructing an actual codeword
agreeing with all received slots outside that union. -/
theorem four_close_folds_recover {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (nodes : Finset K) (four : nodes.card=4)
    (final : K → Fin n → K) (B : Nat)
    (close : ∀ a ∈ nodes,
      (foldedBad encoder inverse2x inverse2y received a (final a)).card ≤ B) :
    ∃ message : Fin (4*n) → K,
      (fibreBad (circleLiftEncoder encoder x y message) received).card ≤ 4*B := by
  classical
  let bad := fun a => foldedBad encoder inverse2x inverse2y received a (final a)
  let union := nodes.biUnion bad
  obtain ⟨message, agrees⟩ := four_support_folds_recover encoder x y inverse2x inverse2y
    hx hy received nodes four final {i | i ∉ union} (by
      intro a ha i hi
      by_contra wrong
      apply hi
      apply Finset.mem_biUnion.mpr
      exact ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ i, wrong⟩⟩)
  refine ⟨message, ?_⟩
  have inclusion : fibreBad (circleLiftEncoder encoder x y message) received ⊆ union := by
    intro i member
    by_contra outside
    obtain ⟨slot, wrong⟩ := (Finset.mem_filter.mp member).2
    exact wrong (agrees i outside slot)
  calc
    (fibreBad (circleLiftEncoder encoder x y message) received).card ≤ union.card :=
      Finset.card_le_card inclusion
    _ ≤ ∑ a ∈ nodes, (bad a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ nodes, B := Finset.sum_le_sum close
    _ = 4*B := by
      simp only [Finset.sum_const, nsmul_eq_mul, four]
      rfl

def closeFoldChallenges {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K))
    (inverse2x inverse2y : Fin m → F) (received : Fin (4*m) → K)
    (B : Nat) (challenges : Finset K) : Finset K := by
  classical
  exact challenges.filter fun a => ∃ final : Fin n → K,
    (foldedBad encoder inverse2x inverse2y received a final).card ≤ B

/-- Far from the full quotient code, at most three challenges permit any
B-close final, including finals selected after the challenge. -/
theorem far_close_fold_challenges_le_three {n m : Nat}
    (encoder : (Fin n → K) →ₗ[K] (Fin m → K)) (x y : Fin m → K)
    (inverse2x inverse2y : Fin m → F)
    (hx : ∀ i, 2*x i*algebraMap F K (inverse2x i)=1)
    (hy : ∀ i, 2*y i*algebraMap F K (inverse2y i)=1)
    (received : Fin (4*m) → K) (B : Nat) (challenges : Finset K)
    (far : ∀ message : Fin (4*n) → K,
      4*B < (fibreBad (circleLiftEncoder encoder x y message) received).card) :
    (closeFoldChallenges encoder inverse2x inverse2y received B challenges).card ≤ 3 := by
  classical
  by_contra notBound
  obtain ⟨nodes, subset, four⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (closeFoldChallenges encoder inverse2x inverse2y received B challenges).card by omega)
  have existsFinal (a : K) (ha : a ∈ nodes) : ∃ final : Fin n → K,
      (foldedBad encoder inverse2x inverse2y received a final).card ≤ B :=
    (Finset.mem_filter.mp (subset ha)).2
  let final : K → Fin n → K := fun a =>
    if ha : a ∈ nodes then Classical.choose (existsFinal a ha) else 0
  have close (a : K) (ha : a ∈ nodes) :
      (foldedBad encoder inverse2x inverse2y received a (final a)).card ≤ B := by
    simpa only [final, dif_pos ha] using Classical.choose_spec (existsFinal a ha)
  obtain ⟨message, distance⟩ := four_close_folds_recover encoder x y inverse2x inverse2y
    hx hy received nodes four final B close
  exact Nat.not_lt_of_ge distance (far message)

#print axioms four_support_folds_recover
#print axioms four_close_folds_recover
#print axioms far_close_fold_challenges_le_three

end
end AspisV8.PartialFoldRecovery

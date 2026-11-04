import Wide.FinalEncoder
import Wide.MatchedInstances
import AspisFormal.CircleNaturalBasisEval
import AspisFormal.V5ComponentCConcreteFoldLinearity
import AspisFormal.V5FriConcreteEncoderApplicability
import AspisFormal.V5FriExactLineDomains
import AspisFormal.V5FriReleasedLineGeometry
import AspisFormal.V5FriBitReverse
import AspisFormal.V5FriNaturalBasisRadix4
import AspisFormal.V7ExactOneFoldDomains

/-! L1: repeated-lift encoder identities for the second fold.
The natural-basis lift retains precisely the coefficient indices divisible
by four. All line-domain and support arguments remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RepeatedLift
open Polynomial Polynomial.Chebyshev
open AspisCircleGroupOrder (g g_pow_2_31)
open AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriNaturalBasisRadix4
open AspisV5FriBitReverse AspisV5FriReleasedLineGeometry
open AspisV5FriExactLineDomains AspisV7ExactOneFoldDomains
open AspisV6OneFoldCandidateExtraction AspisWide.FinalEncoder

/-- Multiplying the basis index by four shifts its selected bits by two. -/
theorem naturalLinePoly_four_mul {K : Type*} [CommRing K] (d : ℕ) :
    naturalLinePoly K (4 * d) = (naturalLinePoly K d).comp (T K 4) := by
  simp only [naturalLinePoly, show 4 * d = 2 ^ 2 * d by omega,
    Nat.bitIndices_two_pow_mul]
  rw [Polynomial.prod_comp]
  rw [show (d.bitIndices.map (fun bit => bit + 2)).toFinset =
      d.bitIndices.toFinset.image (fun bit => bit + 2) by
        ext bit
        simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro bit _
    simpa [pow_add] using (T_mul K (2 ^ bit : ℤ) 4)
  · intro left _ right _ equal
    exact Nat.add_right_cancel equal

abbrev SecondCoefficients (K : Type*) := Fin 64 → K
abbrev SecondWord (K : Type*) := Fin 65536 → K

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Place the second-fold coefficients in slots divisible by four. -/
def liftCoefficients : SecondCoefficients K →ₗ[K] FinalCoefficients K where
  toFun m k := if 4 ∣ k.val then m (parentIndex k) else 0
  map_add' := by
    intro m n
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c m
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- Retain the coefficient slots divisible by four. -/
def projectCoefficients : FinalCoefficients K →ₗ[K] FinalCoefficients K where
  toFun a k := if 4 ∣ k.val then a k else 0
  map_add' := by
    intro a b
    funext k
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro c a
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- Evaluate 64 natural coefficients on the stored log-16 line domain. -/
def secondLinear : SecondCoefficients K →ₗ[K] SecondWord K where
  toFun m v := (naturalCoefficientPolynomial m).eval
    (algebraMap (ZMod AspisCircleGroupOrder.P) K (storedLine16X v))
  map_add' := by
    intro m n
    funext v
    change (naturalCoefficientPolynomial (m + n)).eval _ =
      (naturalCoefficientPolynomial m).eval _ + (naturalCoefficientPolynomial n).eval _
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c m
    funext v
    change (naturalCoefficientPolynomial (c • m)).eval _ =
      c * (naturalCoefficientPolynomial m).eval _
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Repeat a parent value on its four stored children. -/
def repeatWord (word : SecondWord K) : FinalWord K :=
  fun k => word (parentIndex k)

/-- Average the four stored children of each parent. -/
def quartetAverage (word : FinalWord K) : SecondWord K :=
  fun v => (∑ s : Fin 4, word (childIndex v s)) / 4

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
@[simp] theorem liftCoefficients_child (m : SecondCoefficients K) (d : Fin 64)
    (s : Fin 4) :
    liftCoefficients m (childIndex d s) = if s = 0 then m d else 0 := by
  have hd : 4 ∣ (childIndex d s).val ↔ s = 0 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    simp only [childIndex_val]
    constructor
    · intro h
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    · intro h
      subst s
      simp
  change (if 4 ∣ (childIndex d s).val then m (parentIndex (childIndex d s)) else 0) = _
  simp only [hd, parentIndex_childIndex]

/-- The coefficient lift is composition by the fourth Chebyshev polynomial. -/
theorem naturalCoefficientPolynomial_lift (m : SecondCoefficients K) :
    naturalCoefficientPolynomial (liftCoefficients m) =
      (naturalCoefficientPolynomial m).comp (T K 4) := by
  rw [naturalCoefficientPolynomial_eq_basisSum (by norm_num),
    naturalCoefficientPolynomial_eq_basisSum (by norm_num)]
  rw [← (fibreIndexEquiv 64).sum_comp, Fintype.sum_prod_type]
  simp only [fibreIndexEquiv_apply, liftCoefficients_child]
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fin.sum_univ_four]
  simp only [ite_true, Fin.isValue, Fin.reduceEq, ite_false,
    map_zero, zero_mul, add_zero, childIndex_val, add_zero,
    Polynomial.mul_comp, Polynomial.C_comp]
  exact congrArg (fun p => Polynomial.C (m d) * p) (naturalLinePoly_four_mul (K := K) d.val)

/-- The two reversed slot bits contribute a quarter-turn exponent. -/
theorem line18Point_child_exp (v : Fin 65536) (s : Fin 4) :
    line18Point (reverseFin 18 (childIndex v s)) =
      g ^ ((2048 + 8192 * (reverseBits 16 v.val : ℤ)) +
        (2 : ℤ) ^ 29 * (reverseBits 2 s.val : ℤ)) := by
  unfold line18Point reverseFin
  simp only [childIndex_val]
  rw [show reverseBits 18 (4 * v.val + s.val) =
      reverseBits 16 v.val + 65536 * reverseBits 2 s.val by
    simpa using reverseBits_childIndex 16 v.val s]
  apply congrArg (fun exponent : ℤ => g ^ exponent)
  push_cast
  ring

/-- The fourth power of each stored child point is its stored log-16 parent. -/
theorem line18Point_child_pow_four (v : Fin 65536) (s : Fin 4) :
    line18Point (reverseFin 18 (childIndex v s)) ^ 4 =
      line16Point (reverseFin 16 v) := by
  rw [line18Point_child_exp, line16Point, ← zpow_natCast, ← zpow_mul]
  change g ^ (((2048 + 8192 * (reverseBits 16 v.val : ℤ)) +
      (2 : ℤ) ^ 29 * (reverseBits 2 s.val : ℤ)) * 4) =
    g ^ (8192 + 32768 * (reverseBits 16 v.val : ℤ))
  rw [show ((2048 + 8192 * (reverseBits 16 v.val : ℤ)) +
      (2 : ℤ) ^ 29 * (reverseBits 2 s.val : ℤ)) * 4 =
      (8192 + 32768 * (reverseBits 16 v.val : ℤ)) +
        ((2 ^ 31 : ℕ) : ℤ) * (reverseBits 2 s.val : ℤ) by norm_num; ring]
  have horder : g ^ ((2 ^ 31 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact g_pow_2_31
  rw [zpow_add, zpow_mul, horder, one_zpow, mul_one]

omit [Fintype K] [DecidableEq K] in
/-- Two coordinate doublings identify the embedded parent node. -/
theorem storedFirstLineX18_child_T4 (v : Fin 65536) (s : Fin 4) :
    doubledFactor
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))) 2 =
      algebraMap (ZMod AspisCircleGroupOrder.P) K (storedLine16X v) := by
  have hx := congrArg AspisCircleGroupOrder.X (line18Point_child_pow_four v s)
  rw [X_pow_four] at hx
  have hm := congrArg (algebraMap (ZMod AspisCircleGroupOrder.P) K) hx
  simpa only [doubledFactor, storedFirstLineX18, line18X,
    storedLine16X, storedLine16Point, map_sub, map_mul, map_pow, map_ofNat, map_one] using hm

/-- The lifted 256-coefficient encoding repeats the 64-coefficient encoding. -/
theorem exactFinalLinear_lift (m : SecondCoefficients K) (v : Fin 65536) (s : Fin 4) :
    exactFinalLinear (liftCoefficients m) (childIndex v s) = secondLinear m v := by
  have hcheb : doubledFactor
      (algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))) 2 =
      (T K 4).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))) := by
    simpa using doubledFactor_eq_chebyshev
      (algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))) 2
  rw [exactFinalLinear_apply, naturalCoefficientPolynomial_lift, Polynomial.eval_comp,
    ← hcheb, storedFirstLineX18_child_T4]
  rfl

/-- Stored slots zero and one differ by the generator's half-turn. -/
theorem storedFirstLineX18_slot1 (v : Fin 65536) :
    storedFirstLineX18 (childIndex v 1) = -storedFirstLineX18 (childIndex v 0) := by
  change AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 1))) =
    -AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 0)))
  rw [line18Point_child_exp, line18Point_child_exp]
  rw [show reverseBits 2 (1 : Fin 4).val = 2 by rfl,
    show reverseBits 2 (0 : Fin 4).val = 0 by rfl]
  simp only [Nat.cast_ofNat, Nat.cast_zero, mul_zero, add_zero]
  rw [show (2 : ℤ) ^ 29 * 2 = (2 : ℤ) ^ 30 by norm_num]
  exact X_zpow_add_halfTurn _

/-- Stored slots two and three differ by the same half-turn. -/
theorem storedFirstLineX18_slot3 (v : Fin 65536) :
    storedFirstLineX18 (childIndex v 3) = -storedFirstLineX18 (childIndex v 2) := by
  change AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 3))) =
    -AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 2)))
  rw [line18Point_child_exp, line18Point_child_exp]
  rw [show reverseBits 2 (3 : Fin 4).val = 3 by rfl,
    show reverseBits 2 (2 : Fin 4).val = 1 by rfl]
  simp only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  rw [show (2048 + 8192 * (reverseBits 16 v.val : ℤ)) + (2 : ℤ) ^ 29 * 3 =
      ((2048 + 8192 * (reverseBits 16 v.val : ℤ)) + (2 : ℤ) ^ 29) +
        (2 : ℤ) ^ 30 by ring]
  exact X_zpow_add_halfTurn _

/-- Symbolic coordinate doubling, before specializing any concrete generator. -/
theorem doubledFactor_X_sq (p : AspisCircleGroupOrder.C) :
    doubledFactor (AspisCircleGroupOrder.X p) 1 = AspisCircleGroupOrder.X (p ^ 2) :=
  (X_sq p).symm

/-- Squaring the quarter-turn becomes a half-turn, negating the first doubling. -/
theorem storedFirstLineX18_slot2_T2 (v : Fin 65536) :
    doubledFactor (storedFirstLineX18 (childIndex v 2)) 1 =
      -doubledFactor (storedFirstLineX18 (childIndex v 0)) 1 := by
  change doubledFactor (AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 2)))) 1 =
    -doubledFactor (AspisCircleGroupOrder.X (line18Point (reverseFin 18 (childIndex v 0)))) 1
  rw [doubledFactor_X_sq, doubledFactor_X_sq, line18Point_child_exp, line18Point_child_exp]
  rw [show reverseBits 2 (2 : Fin 4).val = 1 by rfl,
    show reverseBits 2 (0 : Fin 4).val = 0 by rfl]
  simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero]
  have hsquare (e : ℤ) : (g ^ e) ^ 2 = g ^ (e * 2) := by
    rw [← zpow_natCast, ← zpow_mul]
    rfl
  rw [hsquare, hsquare]
  rw [show ((2048 + 8192 * (reverseBits 16 v.val : ℤ)) + (2 : ℤ) ^ 29) * 2 =
      (2048 + 8192 * (reverseBits 16 v.val : ℤ)) * 2 + (2 : ℤ) ^ 30 by ring]
  exact X_zpow_add_halfTurn _

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- Projection is the lift of the zero coefficient lane. -/
theorem projectCoefficients_eq_lift (a : FinalCoefficients K) :
    projectCoefficients a = liftCoefficients (coefficientLane 64 0 a) := by
  funext k
  change (if 4 ∣ k.val then a k else 0) =
    (if 4 ∣ k.val then coefficientLane 64 0 a (parentIndex k) else 0)
  by_cases h : 4 ∣ k.val
  · rw [if_pos h, if_pos h]
    change a k = a (childIndex (parentIndex (n := 64) k) 0)
    apply congrArg a
    apply Fin.ext
    simp only [childIndex_val, parentIndex, Fin.val_zero, add_zero]
    exact (Nat.mul_div_cancel' h).symm
  · rw [if_neg h, if_neg h]

/-- Ring maps preserve the symbolic doubling recurrence. -/
theorem doubledFactor_map {L M : Type*} [CommRing L] [CommRing M]
    (f : L →+* M) (x : L) (b : ℕ) :
    f (doubledFactor x b) = doubledFactor (f x) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [doubledFactor, map_sub, map_mul, map_ofNat, map_pow, map_one, ih]

/-- Cancellation of the three nonconstant low factors is a generic ring identity. -/
theorem quartet_low_sum_generic {L : Type*} [CommRing L]
    (x c : Fin 4 → L) (h1 : x 1 = -x 0) (h3 : x 3 = -x 2)
    (h2 : doubledFactor (x 2) 1 = -doubledFactor (x 0) 1) :
    (∑ s : Fin 4, (c 0 + x s * c 1 + doubledFactor (x s) 1 * c 2 +
      x s * doubledFactor (x s) 1 * c 3)) = 4 * c 0 := by
  have hneg (z : L) : doubledFactor (-z) 1 = doubledFactor z 1 := by
    simp only [doubledFactor, neg_sq]
  simp only [Fin.sum_univ_four]
  rw [h1, h3, hneg, hneg, h2]
  ring

omit [Fintype K] [DecidableEq K] in
/-- The four low natural-basis factors average to the constant lane. -/
theorem quartet_low_sum (v : Fin 65536) (c : Fin 4 → K) :
    (∑ s : Fin 4,
      let x := algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))
      c 0 + x * c 1 + doubledFactor x 1 * c 2 + x * doubledFactor x 1 * c 3) = 4 * c 0 := by
  apply quartet_low_sum_generic
    (fun s => algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))) c
  · rw [storedFirstLineX18_slot1, map_neg]
  · rw [storedFirstLineX18_slot3, map_neg]
  · rw [← doubledFactor_map, ← doubledFactor_map, storedFirstLineX18_slot2_T2, map_neg]

/-- The existing radix-four natural-basis expansion at the actual stored children. -/
theorem exactFinalLinear_child_split (a : FinalCoefficients K) (v : Fin 65536) (s : Fin 4) :
    exactFinalLinear a (childIndex v s) =
      let x := algebraMap (ZMod AspisCircleGroupOrder.P) K (storedFirstLineX18 (childIndex v s))
      let c := fun t : Fin 4 => secondLinear (coefficientLane 64 t a) v
      c 0 + x * c 1 + doubledFactor x 1 * c 2 + x * doubledFactor x 1 * c 3 := by
  rw [exactFinalLinear_apply, naturalCoefficientPolynomial_eval_radix4 (by norm_num : 0 < 64),
    storedFirstLineX18_child_T4]
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, one_mul]
  rfl

/-- Averaging an encoded quartet is exactly the projection onto slots divisible by four. -/
theorem exactFinalLinear_project (a : FinalCoefficients K) (v : Fin 65536) (s : Fin 4) :
    exactFinalLinear (projectCoefficients a) (childIndex v s) =
      quartetAverage (exactFinalLinear a) v := by
  rw [projectCoefficients_eq_lift, exactFinalLinear_lift]
  unfold quartetAverage
  simp_rw [exactFinalLinear_child_split]
  rw [quartet_low_sum v (fun t => secondLinear (coefficientLane 64 t a) v)]
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by ring] using
      mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
  exact (mul_div_cancel_left₀ _ h4).symm

/-- Complete quartets above 64 parents exceed the distinct-message overlap cap. -/
theorem exactFinalLinear_descent (a : FinalCoefficients K) (S : Finset (Fin 65536))
    (hconst : ∀ v ∈ S, ∀ s t : Fin 4,
      exactFinalLinear a (childIndex v s) = exactFinalLinear a (childIndex v t))
    (hS : 64 ≤ S.card) :
    a = projectCoefficients a := by
  let support : Finset (Fin 262144) :=
    (S.product (Finset.univ : Finset (Fin 4))).map (fibreIndexEquiv 65536).toEmbedding
  have hcard : support.card = 4 * S.card := by
    simp only [support, Finset.card_map, Finset.product_eq_sprod, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_comm _ _
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by ring] using
      mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
  have hsubset : support ⊆ AspisV5FriCoherentCandidateExtraction.agreementSet
      (exactFinalEncoder a) (exactFinalEncoder (projectCoefficients a)) := by
    intro k hk
    obtain ⟨⟨v, s⟩, hp, rfl⟩ := Finset.mem_map.mp hk
    have hv : v ∈ S := (Finset.mem_product.mp hp).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change exactFinalLinear a (childIndex v s) =
      exactFinalLinear (projectCoefficients a) (childIndex v s)
    rw [exactFinalLinear_project]
    unfold quartetAverage
    have hsum : (∑ t : Fin 4, exactFinalLinear a (childIndex v t)) =
        (4 : K) * exactFinalLinear a (childIndex v s) := by
      calc
        _ = ∑ t : Fin 4, exactFinalLinear a (childIndex v s) :=
          Finset.sum_congr rfl (fun t _ => hconst v hv t s)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_ofNat]
    rw [hsum]
    exact (mul_div_cancel_left₀ _ h4).symm
  by_contra hne
  have hcap := exactFinalEncoder_overlap_cap a (projectCoefficients a) hne
  have hle := Finset.card_le_card hsubset
  rw [hcard] at hle
  omega

/-- Descent identifies the surviving 64 natural coefficients explicitly. -/
theorem exactFinalLinear_descent_lift (a : FinalCoefficients K) (S : Finset (Fin 65536))
    (hconst : ∀ v ∈ S, ∀ s t : Fin 4,
      exactFinalLinear a (childIndex v s) = exactFinalLinear a (childIndex v t))
    (hS : 64 ≤ S.card) :
    ∃ m : SecondCoefficients K, a = liftCoefficients m := by
  refine ⟨coefficientLane 64 0 a, ?_⟩
  exact (exactFinalLinear_descent a S hconst hS).trans (projectCoefficients_eq_lift a)

@[simp] theorem repeatWord_child {L : Type} (word : SecondWord L)
    (v : Fin 65536) (s : Fin 4) :
    repeatWord word (childIndex v s) = word v := by
  simp only [repeatWord, parentIndex_childIndex]

#print axioms exactFinalLinear_descent
#print axioms exactFinalLinear_descent_lift

#print axioms exactFinalLinear_project

#print axioms line18Point_child_pow_four
#print axioms storedFirstLineX18_child_T4
#print axioms exactFinalLinear_lift

#print axioms naturalLinePoly_four_mul
#print axioms naturalCoefficientPolynomial_lift
end AspisR1.RepeatedLift

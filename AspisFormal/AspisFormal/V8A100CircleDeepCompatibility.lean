import AspisFormal.V8A100TwoPointDeep
import AspisFormal.V8A100CircleChordQuotient

/-!
# V8-A100 two-point DEEP compatibility with the deployed circle encoder

This bridge instantiates the coordinate-ring quotient with the exact rational
secure-circle map, the exact 1024-coefficient message split, and the same
coordinate-adaptive interpolant used by the Rust research path.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace AspisV8A100CircleDeepCompatibility

open Polynomial
open AspisV8A100TwoPointDeep
open AspisV8A100CircleChordQuotient
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisV6Width29CorrelatedAgreement

variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Squared chord length for two rational-circle parameters. -/
theorem rational_chordNormLeading
    (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0) :
    chordNormLeading
        (rationalCircleX t0) (rationalCircleY t0)
        (rationalCircleX t1) (rationalCircleY t1) =
      4 * (t1 - t0) ^ 2 /
        (circleDenominator t0 * circleDenominator t1) := by
  simp only [chordNormLeading, chordU, chordV, rationalCircleX,
    rationalCircleY]
  field_simp [finite0, finite1]
  simp only [circleDenominator]
  ring

theorem rational_chordNormLeading_ne_zero
    (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1) :
    chordNormLeading
        (rationalCircleX t0) (rationalCircleY t0)
        (rationalCircleX t1) (rationalCircleY t1) ≠ 0 := by
  rw [rational_chordNormLeading t0 t1 finite0 finite1]
  have twoNe : (2 : K) ≠ 0 := NeZero.ne 2
  have fourNe : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero twoNe twoNe
  exact div_ne_zero
    (mul_ne_zero fourNe (pow_ne_zero 2 (sub_ne_zero.mpr distinct.symm)))
    (mul_ne_zero finite0 finite1)

noncomputable def affinePolynomialInterpolant
    (h0 h1 a b : K) : K[X] :=
  C a + C ((b - a) / (h1 - h0)) * (X - C h0)

theorem affinePolynomialInterpolant_eval
    (h0 h1 a b h : K) :
    (affinePolynomialInterpolant h0 h1 a b).eval h =
      affineCoordinateInterpolant h0 h1 a b h := by
  simp [affinePolynomialInterpolant, affineCoordinateInterpolant]
  ring

theorem affinePolynomialInterpolant_natDegree_le
    (h0 h1 a b : K) :
    (affinePolynomialInterpolant h0 h1 a b).natDegree ≤ 1 := by
  unfold affinePolynomialInterpolant
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))

noncomputable def coordinateResidual0
    (p0 : K[X]) (h0 h1 a b : K) : K[X] :=
  p0 - affinePolynomialInterpolant h0 h1 a b

theorem coordinateResidual0_natDegree_le
    (p0 : K[X]) (h0 h1 a b : K) (degree0 : p0.natDegree ≤ 511) :
    (coordinateResidual0 p0 h0 h1 a b).natDegree ≤ 511 := by
  unfold coordinateResidual0
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le degree0
      ((affinePolynomialInterpolant_natDegree_le _ _ _ _).trans (by omega)))

theorem coordinateResidual_at_first
    (p0 p1 : K[X]) (h0 h1 y0 a b : K)
    (value0 : p0.eval h0 + y0 * p1.eval h0 = a) :
    (coordinateResidual0 p0 h0 h1 a b).eval h0 +
      y0 * p1.eval h0 = 0 := by
  rw [coordinateResidual0, Polynomial.eval_sub,
    affinePolynomialInterpolant_eval,
    affineCoordinateInterpolant_at_first]
  linear_combination value0

theorem coordinateResidual_at_second
    (p0 p1 : K[X]) (h0 h1 y1 a b : K)
    (distinctH : h0 ≠ h1)
    (value1 : p0.eval h1 + y1 * p1.eval h1 = b) :
    (coordinateResidual0 p0 h0 h1 a b).eval h1 +
      y1 * p1.eval h1 = 0 := by
  rw [coordinateResidual0, Polynomial.eval_sub,
    affinePolynomialInterpolant_eval]
  rw [affineCoordinateInterpolant_at_second _ _ _ _ distinctH]
  linear_combination value1

theorem coordinateResidual_eval
    (p0 p1 : K[X]) (h0 h1 a b x y : K) :
    (coordinateResidual0 p0 h0 h1 a b).eval x + y * p1.eval x =
      (p0.eval x + y * p1.eval x) -
        affineCoordinateInterpolant h0 h1 a b x := by
  rw [coordinateResidual0, Polynomial.eval_sub,
    affinePolynomialInterpolant_eval]
  ring

/-- Exact compatibility for the Rust branch that interpolates in `x`.
The quotient evaluated at every finite non-OOD rational circle point is the
evaluation of a circle polynomial with the proven one-degree drop. -/
theorem initialCircle_distinctX_deep_compatible
    (message : Fin 1024 → K) (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1)
    (distinctX : rationalCircleX t0 ≠ rationalCircleX t1) :
    ∃ g0 g1 : K[X],
      g0.natDegree ≤ 511 ∧ g1.natDegree ≤ 510 ∧
      ∀ t : K, circleDenominator t ≠ 0 → t ≠ t0 → t ≠ t1 →
        affineChordDeepQuotient
            (initialCircleValue message t)
            (rationalCircleX t0) (rationalCircleX t1)
            (initialCircleValue message t0) (initialCircleValue message t1)
            (rationalCircleX t) (circleChordZerofier t0 t1 t) =
          g0.eval (rationalCircleX t) +
            rationalCircleY t * g1.eval (rationalCircleX t) := by
  let p0 : K[X] := initialP0 message
  let p1 : K[X] := initialP1 message
  let x0 := rationalCircleX t0
  let y0 := rationalCircleY t0
  let x1 := rationalCircleX t1
  let y1 := rationalCircleY t1
  let a := initialCircleValue message t0
  let b := initialCircleValue message t1
  let r0 : K[X] := coordinateResidual0 p0 x0 x1 a b
  let r1 : K[X] := p1
  have p0Degree : p0.natDegree ≤ 511 := by
    dsimp only [p0]
    have h := initialP0_degree_lt message
    omega
  have p1Degree : p1.natDegree ≤ 511 := by
    dsimp only [p1]
    have h := initialP1_degree_lt message
    omega
  have value0 : p0.eval x0 + y0 * p1.eval x0 = a := by
    rfl
  have value1 : p0.eval x1 + y1 * p1.eval x1 = b := by
    rfl
  obtain ⟨g0, g1, multiplied0, multiplied1, degree0, degree1⟩ :=
    distinctX_circleChord_quotient_exists
      x0 y0 x1 y1
      r0 r1
      (rationalCircle_on_circle t0 finite0)
      (rationalCircle_on_circle t1 finite1)
      distinctX
      (rational_chordNormLeading_ne_zero t0 t1 finite0 finite1 distinct)
      (coordinateResidual0_natDegree_le p0 x0 x1 a b p0Degree)
      p1Degree
      (coordinateResidual_at_first p0 p1 x0 x1 y0 a b value0)
      (coordinateResidual_at_second p0 p1 x0 x1 y1 a b distinctX value1)
  refine ⟨g0, g1, degree0, degree1, ?_⟩
  intro t finite notFirst notSecond
  have onCircle := rationalCircle_on_circle t finite
  have product := circleLineMul_eval
    x0 y0 x1 y1
    (rationalCircleX t) (rationalCircleY t) g0 g1 onCircle
  rw [multiplied0, multiplied1] at product
  have residualValue :
      r0.eval (rationalCircleX t) +
          rationalCircleY t * r1.eval (rationalCircleX t) =
        initialCircleValue message t -
          affineCoordinateInterpolant
            (rationalCircleX t0) (rationalCircleX t1)
            (initialCircleValue message t0) (initialCircleValue message t1)
            (rationalCircleX t) := by
    have currentValue :
        p0.eval (rationalCircleX t) +
            rationalCircleY t * p1.eval (rationalCircleX t) =
          initialCircleValue message t := by
      rfl
    calc
      r0.eval (rationalCircleX t) +
          rationalCircleY t * r1.eval (rationalCircleX t) =
        (p0.eval (rationalCircleX t) +
            rationalCircleY t * p1.eval (rationalCircleX t)) -
          affineCoordinateInterpolant x0 x1 a b
            (rationalCircleX t) :=
        coordinateResidual_eval p0 p1 x0 x1 a b
          (rationalCircleX t) (rationalCircleY t)
      _ = _ := by rw [currentValue]
  have chordValue :
      chordC (rationalCircleX t0) (rationalCircleY t0)
          (rationalCircleX t1) (rationalCircleY t1) +
        chordU (rationalCircleY t0) (rationalCircleY t1) *
          rationalCircleX t +
        chordV (rationalCircleX t0) (rationalCircleX t1) *
          rationalCircleY t = circleChordZerofier t0 t1 t := by
    rfl
  rw [residualValue, chordValue] at product
  have chordNonzero := circleChordZerofier_ne_zero
    t0 t1 t finite0 finite1 finite distinct notFirst notSecond
  unfold affineChordDeepQuotient
  apply (div_eq_iff chordNonzero).2
  simpa only [mul_comm] using product

def affineCoordinateSlope (h0 h1 a b : K) : K :=
  (b - a) / (h1 - h0)

noncomputable def yResidual0
    (p0 : K[X]) (y0 y1 a b : K) : K[X] :=
  p0 - C (a - affineCoordinateSlope y0 y1 a b * y0)

noncomputable def yResidual1
    (p1 : K[X]) (y0 y1 a b : K) : K[X] :=
  p1 - C (affineCoordinateSlope y0 y1 a b)

theorem yResidual0_natDegree_le
    (p0 : K[X]) (y0 y1 a b : K) (degree0 : p0.natDegree ≤ 511) :
    (yResidual0 p0 y0 y1 a b).natDegree ≤ 511 := by
  unfold yResidual0
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le degree0 (by rw [Polynomial.natDegree_C]; omega))

theorem yResidual1_natDegree_le
    (p1 : K[X]) (y0 y1 a b : K) (degree1 : p1.natDegree ≤ 511) :
    (yResidual1 p1 y0 y1 a b).natDegree ≤ 511 := by
  unfold yResidual1
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le degree1 (by simp))

theorem yResidual_eval
    (p0 p1 : K[X]) (y0 y1 a b x y : K) :
    (yResidual0 p0 y0 y1 a b).eval x +
        y * (yResidual1 p1 y0 y1 a b).eval x =
      (p0.eval x + y * p1.eval x) -
        affineCoordinateInterpolant y0 y1 a b y := by
  simp only [yResidual0, yResidual1, Polynomial.eval_sub,
    Polynomial.eval_C, affineCoordinateSlope, affineCoordinateInterpolant]
  ring

theorem yResidual_at_first
    (p0 p1 : K[X]) (x y0 y1 a b : K)
    (value0 : p0.eval x + y0 * p1.eval x = a) :
    (yResidual0 p0 y0 y1 a b).eval x +
      y0 * (yResidual1 p1 y0 y1 a b).eval x = 0 := by
  rw [yResidual_eval]
  rw [affineCoordinateInterpolant_at_first]
  linear_combination value0

theorem yResidual_at_second
    (p0 p1 : K[X]) (x y0 y1 a b : K)
    (distinctY : y0 ≠ y1)
    (value1 : p0.eval x + y1 * p1.eval x = b) :
    (yResidual0 p0 y0 y1 a b).eval x +
      y1 * (yResidual1 p1 y0 y1 a b).eval x = 0 := by
  rw [yResidual_eval]
  rw [affineCoordinateInterpolant_at_second _ _ _ _ distinctY]
  linear_combination value1

/-- Exact compatibility for the Rust fallback branch where the two secure
circle points share `x` and interpolation therefore uses `y`. -/
theorem initialCircle_equalX_deep_compatible
    (message : Fin 1024 → K) (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1)
    (equalX : rationalCircleX t0 = rationalCircleX t1) :
    ∃ g0 g1 : K[X],
      g0.natDegree ≤ 511 ∧ g1.natDegree ≤ 510 ∧
      ∀ t : K, circleDenominator t ≠ 0 → t ≠ t0 → t ≠ t1 →
        affineChordDeepQuotient
            (initialCircleValue message t)
            (rationalCircleY t0) (rationalCircleY t1)
            (initialCircleValue message t0) (initialCircleValue message t1)
            (rationalCircleY t) (circleChordZerofier t0 t1 t) =
          g0.eval (rationalCircleX t) +
            rationalCircleY t * g1.eval (rationalCircleX t) := by
  let p0 : K[X] := initialP0 message
  let p1 : K[X] := initialP1 message
  let x := rationalCircleX t0
  let y0 := rationalCircleY t0
  let y1 := rationalCircleY t1
  let a := initialCircleValue message t0
  let b := initialCircleValue message t1
  have distinctY : y0 ≠ y1 := by
    intro equalY
    apply distinct
    apply rationalCircle_pair_injective finite0 finite1
    exact Prod.ext equalX equalY
  let r0 : K[X] := yResidual0 p0 y0 y1 a b
  let r1 : K[X] := yResidual1 p1 y0 y1 a b
  have p0Degree : p0.natDegree ≤ 511 := by
    dsimp only [p0]
    have h := initialP0_degree_lt message
    omega
  have p1Degree : p1.natDegree ≤ 511 := by
    dsimp only [p1]
    have h := initialP1_degree_lt message
    omega
  have value0 : p0.eval x + y0 * p1.eval x = a := by
    rfl
  have value1 : p0.eval x + y1 * p1.eval x = b := by
    have raw :
        p0.eval (rationalCircleX t1) +
            rationalCircleY t1 * p1.eval (rationalCircleX t1) =
          initialCircleValue message t1 := by
      rfl
    simpa only [x, y1, b, equalX] using raw
  obtain ⟨g0, g1, multiplied0, multiplied1, degree0, degree1⟩ :=
    equalX_circleChord_quotient_exists x y0 y1 r0 r1 distinctY
      (yResidual0_natDegree_le p0 y0 y1 a b p0Degree)
      (yResidual1_natDegree_le p1 y0 y1 a b p1Degree)
      (yResidual_at_first p0 p1 x y0 y1 a b value0)
      (yResidual_at_second p0 p1 x y0 y1 a b distinctY value1)
  refine ⟨g0, g1, degree0.trans (by omega), degree1, ?_⟩
  intro t finite notFirst notSecond
  have onCircle := rationalCircle_on_circle t finite
  have product := circleLineMul_eval x y0 x y1
    (rationalCircleX t) (rationalCircleY t) g0 g1 onCircle
  rw [multiplied0, multiplied1] at product
  have currentValue :
      p0.eval (rationalCircleX t) +
          rationalCircleY t * p1.eval (rationalCircleX t) =
        initialCircleValue message t := by
    rfl
  have residualValue :
      r0.eval (rationalCircleX t) +
          rationalCircleY t * r1.eval (rationalCircleX t) =
        initialCircleValue message t -
          affineCoordinateInterpolant y0 y1 a b (rationalCircleY t) := by
    calc
      r0.eval (rationalCircleX t) +
          rationalCircleY t * r1.eval (rationalCircleX t) =
        (p0.eval (rationalCircleX t) +
            rationalCircleY t * p1.eval (rationalCircleX t)) -
          affineCoordinateInterpolant y0 y1 a b (rationalCircleY t) :=
        yResidual_eval p0 p1 y0 y1 a b
          (rationalCircleX t) (rationalCircleY t)
      _ = _ := by rw [currentValue]
  have chordValue :
      chordC x y0 x y1 + chordU y0 y1 * rationalCircleX t +
          chordV x x * rationalCircleY t =
        circleChordZerofier t0 t1 t := by
    simp only [circleChordZerofier]
    rw [← equalX]
    rfl
  rw [residualValue, chordValue] at product
  have chordNonzero := circleChordZerofier_ne_zero
    t0 t1 t finite0 finite1 finite distinct notFirst notSecond
  unfold affineChordDeepQuotient
  apply (div_eq_iff chordNonzero).2
  simpa only [mul_comm] using product

noncomputable def adaptiveDeepCoordinate (t0 t1 t : K) : K := by
  classical
  exact if rationalCircleX t0 = rationalCircleX t1 then
      rationalCircleY t
    else
      rationalCircleX t

/-- Combined theorem matching the source branch exactly: use `x` whenever
the endpoint x-coordinates differ and `y` otherwise. -/
theorem initialCircle_adaptive_deep_compatible
    (message : Fin 1024 → K) (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1) :
    ∃ g0 g1 : K[X],
      g0.natDegree ≤ 511 ∧ g1.natDegree ≤ 510 ∧
      ∀ t : K, circleDenominator t ≠ 0 → t ≠ t0 → t ≠ t1 →
        affineChordDeepQuotient
            (initialCircleValue message t)
            (adaptiveDeepCoordinate t0 t1 t0)
            (adaptiveDeepCoordinate t0 t1 t1)
            (initialCircleValue message t0) (initialCircleValue message t1)
            (adaptiveDeepCoordinate t0 t1 t)
            (circleChordZerofier t0 t1 t) =
          g0.eval (rationalCircleX t) +
            rationalCircleY t * g1.eval (rationalCircleX t) := by
  classical
  by_cases equalX : rationalCircleX t0 = rationalCircleX t1
  · simpa only [adaptiveDeepCoordinate, if_pos equalX] using
      initialCircle_equalX_deep_compatible message t0 t1
        finite0 finite1 distinct equalX
  · simpa only [adaptiveDeepCoordinate, if_neg equalX] using
      initialCircle_distinctX_deep_compatible message t0 t1
        finite0 finite1 distinct equalX

def mergeEvenOdd {n : Nat}
    (even odd : Fin n → K) (index : Fin (2 * n)) : K :=
  if index.val % 2 = 0 then
    even ⟨index.val / 2, by omega⟩
  else
    odd ⟨index.val / 2, by omega⟩

theorem evenCoefficients_mergeEvenOdd {n : Nat}
    (even odd : Fin n → K) :
    evenCoefficients (mergeEvenOdd even odd) = even := by
  funext index
  simp [evenCoefficients, mergeEvenOdd]

theorem oddCoefficients_mergeEvenOdd {n : Nat}
    (even odd : Fin n → K) :
    oddCoefficients (mergeEvenOdd even odd) = odd := by
  funext index
  have half : (2 * index.val + 1) / 2 = index.val := by omega
  simp [oddCoefficients, mergeEvenOdd, half]

/-- Every pair in the quotient degree range is represented by an actual
1024-entry natural-basis message consumed by the deployed initial encoder. -/
theorem circlePair_has_initialMessage
    (g0 g1 : K[X])
    (degree0 : g0.natDegree ≤ 511)
    (degree1 : g1.natDegree ≤ 510) :
    ∃ message : Fin 1024 → K,
      initialP0 message = g0 ∧ initialP1 message = g1 := by
  obtain ⟨even, evenPolynomial⟩ :=
    naturalCoefficientPolynomial_complete (K := K) (n := 512)
      (by norm_num) g0 (by simpa using degree0)
  obtain ⟨odd, oddPolynomial⟩ :=
    naturalCoefficientPolynomial_complete (K := K) (n := 512)
      (by norm_num) g1 (by omega)
  let message : Fin 1024 → K := mergeEvenOdd even odd
  refine ⟨message, ?_, ?_⟩
  · rw [initialP0, show evenCoefficients message = even by
      simpa only [message] using evenCoefficients_mergeEvenOdd even odd]
    exact evenPolynomial
  · rw [initialP1, show oddCoefficients message = odd by
      simpa only [message] using oddCoefficients_mergeEvenOdd even odd]
    exact oddPolynomial

/-- The adaptive quotient is not merely an abstract low-degree pair: it has
an exact deployed initial-message representative. -/
theorem initialCircle_adaptive_deep_has_message
    (message : Fin 1024 → K) (t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1) :
    ∃ quotientMessage : Fin 1024 → K,
      ∀ t : K, circleDenominator t ≠ 0 → t ≠ t0 → t ≠ t1 →
        affineChordDeepQuotient
            (initialCircleValue message t)
            (adaptiveDeepCoordinate t0 t1 t0)
            (adaptiveDeepCoordinate t0 t1 t1)
            (initialCircleValue message t0) (initialCircleValue message t1)
            (adaptiveDeepCoordinate t0 t1 t)
            (circleChordZerofier t0 t1 t) =
          initialCircleValue quotientMessage t := by
  obtain ⟨g0, g1, degree0, degree1, compatible⟩ :=
    initialCircle_adaptive_deep_compatible message t0 t1
      finite0 finite1 distinct
  obtain ⟨quotientMessage, p0, p1⟩ :=
    circlePair_has_initialMessage g0 g1 degree0 degree1
  refine ⟨quotientMessage, ?_⟩
  intro t finite notFirst notSecond
  rw [compatible t finite notFirst notSecond]
  simp only [initialCircleValue, p0, p1]

/-- Width-29 component batching, the two public component-evaluation vectors,
and the adaptive chord quotient together produce an actual initial-encoder
message.  This is the exact no-new-tree algebraic object used by V8. -/
theorem width29_adaptive_deep_has_message
    (components : Fin 29 → Fin 1024 → K) (gamma t0 t1 : K)
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (distinct : t0 ≠ t1) :
    ∃ quotientMessage : Fin 1024 → K,
      ∀ t : K, circleDenominator t ≠ 0 → t ≠ t0 → t ≠ t1 →
        affineChordDeepQuotient
            (width29Batch
              (fun lane => initialCircleValue (components lane) t) gamma)
            (adaptiveDeepCoordinate t0 t1 t0)
            (adaptiveDeepCoordinate t0 t1 t1)
            (width29Batch
              (fun lane => initialCircleValue (components lane) t0) gamma)
            (width29Batch
              (fun lane => initialCircleValue (components lane) t1) gamma)
            (adaptiveDeepCoordinate t0 t1 t)
            (circleChordZerofier t0 t1 t) =
          initialCircleValue quotientMessage t := by
  obtain ⟨quotientMessage, compatible⟩ :=
    initialCircle_adaptive_deep_has_message
      (width29BatchMessage components gamma) t0 t1 finite0 finite1 distinct
  refine ⟨quotientMessage, ?_⟩
  intro t finite notFirst notSecond
  simpa only [initialCircleValue_width29BatchMessage] using
    compatible t finite notFirst notSecond

#print axioms rational_chordNormLeading
#print axioms rational_chordNormLeading_ne_zero
#print axioms affinePolynomialInterpolant_eval
#print axioms initialCircle_distinctX_deep_compatible
#print axioms initialCircle_equalX_deep_compatible
#print axioms initialCircle_adaptive_deep_compatible
#print axioms circlePair_has_initialMessage
#print axioms initialCircle_adaptive_deep_has_message
#print axioms width29_adaptive_deep_has_message

end AspisV8A100CircleDeepCompatibility

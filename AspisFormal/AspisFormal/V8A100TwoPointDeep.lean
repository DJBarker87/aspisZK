import AspisFormal.Pool.V7CombinedCandidateExact
import AspisFormal.K1.V7Tag73SecureCircleMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# V8-A100 two-point circle-DEEP algebra

This file isolates the algebra that a V8 verifier would need before changing
the production transcript or FRI path.  The OOD points use the same rational
circle chart as `secure_ood_circle_point_from_parameter` in Rust.  The
component evaluator uses the actual 1024-coefficient natural circle message,
and the batching theorem uses the deployed width-29 gamma convention.

The ordinary polynomial section proves the exact two-root factorisation and
degree drop.  Connecting that factorisation to the four-round source verifier
is deliberately a separate source-refinement obligation; no such connection
is assumed here.
-/

set_option autoImplicit false

namespace AspisV8A100TwoPointDeep

open Polynomial
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriCircleEncoderDistance
open AspisV6Width29CorrelatedAgreement
open AspisCircleTensorBinding

/-! ## The exact rational circle chart used by Rust -/

variable {K : Type*} [Field K]

def circleDenominator (t : K) : K := 1 + t ^ 2

def rationalCircleX (t : K) : K :=
  (1 - t ^ 2) / circleDenominator t

def rationalCircleY (t : K) : K :=
  (2 * t) / circleDenominator t

theorem rationalCircle_on_circle [NeZero (2 : K)]
    (t : K) (finite : circleDenominator t ≠ 0) :
    rationalCircleX t ^ 2 + rationalCircleY t ^ 2 = 1 := by
  unfold rationalCircleX rationalCircleY
  rw [div_pow, div_pow]
  field_simp [finite]
  simp only [circleDenominator]
  ring

theorem rationalCircle_one_add_x_ne_zero [NeZero (2 : K)]
    (t : K) (finite : circleDenominator t ≠ 0) :
    1 + rationalCircleX t ≠ 0 := by
  have twoNe : (2 : K) ≠ 0 := NeZero.ne 2
  have identity :
      1 + rationalCircleX t = 2 / circleDenominator t := by
    unfold rationalCircleX
    field_simp [finite]
    simp only [circleDenominator]
    ring
  rw [identity]
  exact div_ne_zero twoNe finite

/-- The source rational map retains its parameter through the usual inverse
`t = y / (1+x)`.  This is the exact injectivity fact needed to reason about
two independently sampled secure-circle parameters. -/
theorem stereo_rationalCircle [NeZero (2 : K)]
    (t : K) (finite : circleDenominator t ≠ 0) :
    rationalCircleY t / (1 + rationalCircleX t) = t := by
  have twoNe : (2 : K) ≠ 0 := NeZero.ne 2
  have xIdentity :
      1 + rationalCircleX t = 2 / circleDenominator t := by
    unfold rationalCircleX
    field_simp [finite]
    simp only [circleDenominator]
    ring
  rw [xIdentity]
  unfold rationalCircleY
  field_simp [finite, twoNe]

theorem rationalCircle_pair_injective [NeZero (2 : K)]
    {t0 t1 : K}
    (finite0 : circleDenominator t0 ≠ 0)
    (finite1 : circleDenominator t1 ≠ 0)
    (same : (rationalCircleX t0, rationalCircleY t0) =
      (rationalCircleX t1, rationalCircleY t1)) :
    t0 = t1 := by
  have xSame := congrArg Prod.fst same
  have ySame := congrArg Prod.snd same
  change rationalCircleX t0 = rationalCircleX t1 at xSame
  change rationalCircleY t0 = rationalCircleY t1 at ySame
  calc
    t0 = rationalCircleY t0 / (1 + rationalCircleX t0) :=
      (stereo_rationalCircle t0 finite0).symm
    _ = rationalCircleY t1 / (1 + rationalCircleX t1) := by
      rw [xSame, ySame]
    _ = t1 := stereo_rationalCircle t1 finite1

/-! ## Two-point interpolation and zerofier -/

def twoPointInterpolant (t0 t1 a b t : K) : K :=
  a + (b - a) * (t - t0) / (t1 - t0)

def twoPointZerofier (t0 t1 t : K) : K :=
  (t - t0) * (t - t1)

theorem twoPointInterpolant_at_first
    (t0 t1 a b : K) :
    twoPointInterpolant t0 t1 a b t0 = a := by
  simp [twoPointInterpolant]

theorem twoPointInterpolant_at_second
    (t0 t1 a b : K) (distinct : t0 ≠ t1) :
    twoPointInterpolant t0 t1 a b t1 = b := by
  have denominator : t1 - t0 ≠ 0 := sub_ne_zero.mpr distinct.symm
  unfold twoPointInterpolant
  field_simp [denominator]
  ring

theorem twoPointZerofier_eq_zero_iff
    (t0 t1 t : K) :
    twoPointZerofier t0 t1 t = 0 ↔ t = t0 ∨ t = t1 := by
  constructor
  · intro zero
    rcases mul_eq_zero.mp zero with first | second
    · exact Or.inl (sub_eq_zero.mp first)
    · exact Or.inr (sub_eq_zero.mp second)
  · rintro (rfl | rfl) <;> simp [twoPointZerofier]

theorem twoPointZerofier_ne_zero
    (t0 t1 t : K) (notFirst : t ≠ t0) (notSecond : t ≠ t1) :
    twoPointZerofier t0 t1 t ≠ 0 := by
  rw [ne_eq, twoPointZerofier_eq_zero_iff]
  exact not_or_intro notFirst notSecond

def twoPointDeepQuotient
    (received : K → K) (t0 t1 a b t : K) : K :=
  (received t - twoPointInterpolant t0 t1 a b t) /
    twoPointZerofier t0 t1 t

/-! ## Actual 1024-coefficient circle messages and width-29 batching -/

noncomputable def initialCircleValue (message : Fin 1024 → K) (t : K) : K :=
  (initialP0 message).eval (rationalCircleX t) +
    rationalCircleY t * (initialP1 message).eval (rationalCircleX t)

def width29BatchMessage
    (components : Fin 29 → Fin 1024 → K) (gamma : K) : Fin 1024 → K :=
  fun row => width29Batch (fun lane => components lane row) gamma

theorem naturalCoefficientPolynomial_eval_width29Batch [NeZero (2 : K)]
    {n : Nat} (positive : 0 < n)
    (components : Fin 29 → Fin n → K) (gamma x : K) :
    (naturalCoefficientPolynomial
        (fun coefficient =>
          width29Batch (fun lane => components lane coefficient) gamma)).eval x =
      width29Batch
        (fun lane => (naturalCoefficientPolynomial (components lane)).eval x)
        gamma := by
  calc
    (naturalCoefficientPolynomial
        (fun coefficient =>
          width29Batch (fun lane => components lane coefficient) gamma)).eval x =
        ∑ coefficient : Fin n,
          (∑ lane : Fin 29,
              components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      rw [naturalCoefficientPolynomial_eval_eq_sum positive]
      rfl
    _ = ∑ coefficient : Fin n, ∑ lane : Fin 29,
          (components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      apply Finset.sum_congr rfl
      intro coefficient _
      rw [Finset.sum_mul]
    _ = ∑ lane : Fin 29, ∑ coefficient : Fin n,
          (components lane coefficient * gamma ^ lane.val) *
            naturalLineValue x coefficient := by
      rw [Finset.sum_comm]
    _ = ∑ lane : Fin 29,
          (∑ coefficient : Fin n,
              components lane coefficient * naturalLineValue x coefficient) *
            gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro coefficient _
      ring
    _ = ∑ lane : Fin 29,
          (naturalCoefficientPolynomial (components lane)).eval x *
            gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [naturalCoefficientPolynomial_eval_eq_sum positive]
    _ = width29Batch
          (fun lane => (naturalCoefficientPolynomial (components lane)).eval x)
          gamma := by
      rfl

theorem initialP0_eval_width29BatchMessage [NeZero (2 : K)]
    (components : Fin 29 → Fin 1024 → K) (gamma x : K) :
    (initialP0 (width29BatchMessage components gamma)).eval x =
      width29Batch (fun lane => (initialP0 (components lane)).eval x) gamma := by
  unfold initialP0
  have coefficientBatch :
      evenCoefficients (width29BatchMessage components gamma) =
        fun coefficient : Fin 512 =>
          width29Batch
            (fun lane => evenCoefficients (components lane) coefficient) gamma := by
    funext coefficient
    rfl
  rw [coefficientBatch]
  exact naturalCoefficientPolynomial_eval_width29Batch
    (by norm_num) _ gamma x

theorem initialP1_eval_width29BatchMessage [NeZero (2 : K)]
    (components : Fin 29 → Fin 1024 → K) (gamma x : K) :
    (initialP1 (width29BatchMessage components gamma)).eval x =
      width29Batch (fun lane => (initialP1 (components lane)).eval x) gamma := by
  unfold initialP1
  have coefficientBatch :
      oddCoefficients (width29BatchMessage components gamma) =
        fun coefficient : Fin 512 =>
          width29Batch
            (fun lane => oddCoefficients (components lane) coefficient) gamma := by
    funext coefficient
    rfl
  rw [coefficientBatch]
  exact naturalCoefficientPolynomial_eval_width29Batch
    (by norm_num) _ gamma x

/-- Component-wise OOD evaluation commutes with the actual width-29 gamma
batch.  The first 26 M31 components enter this theorem through the same
algebra-map embedding used by their QM31 messages; the last three are native
QM31 messages. -/
theorem initialCircleValue_width29BatchMessage [NeZero (2 : K)]
    (components : Fin 29 → Fin 1024 → K) (gamma t : K) :
    initialCircleValue (width29BatchMessage components gamma) t =
      width29Batch (fun lane => initialCircleValue (components lane) t) gamma := by
  unfold initialCircleValue
  rw [initialP0_eval_width29BatchMessage,
    initialP1_eval_width29BatchMessage]
  unfold width29Batch
  rw [Finset.mul_sum]
  calc
    (∑ lane : Fin 29,
        (initialP0 (components lane)).eval (rationalCircleX t) *
          gamma ^ lane.val) +
        ∑ lane : Fin 29,
          rationalCircleY t *
            ((initialP1 (components lane)).eval (rationalCircleX t) *
              gamma ^ lane.val) =
      ∑ lane : Fin 29,
        ((initialP0 (components lane)).eval (rationalCircleX t) *
            gamma ^ lane.val +
          rationalCircleY t *
            ((initialP1 (components lane)).eval (rationalCircleX t) *
              gamma ^ lane.val)) := (Finset.sum_add_distrib).symm
    _ = ∑ lane : Fin 29,
        ((initialP0 (components lane)).eval (rationalCircleX t) +
          rationalCircleY t *
            (initialP1 (components lane)).eval (rationalCircleX t)) *
          gamma ^ lane.val := by
      apply Finset.sum_congr rfl
      intro lane _
      ring

/-- The exact cleared stereographic numerator evaluates to the source-shaped
circle value times the common nonzero denominator.  This is the bridge from
the deployed rational map to the degree-1024 root count. -/
theorem circleNumerator_eval_initialCircleValue [NeZero (2 : K)]
    (message : Fin 1024 → K) (t : K)
    (finite : circleDenominator t ≠ 0) :
    (circleNumerator (initialP0 message) (initialP1 message)).eval t =
      circleDenominator t ^ 512 * initialCircleValue message t := by
  have onCircle := rationalCircle_on_circle t finite
  have oneAddX := rationalCircle_one_add_x_ne_zero t finite
  have notWest : rationalCircleX t ≠ -1 := by
    intro west
    apply oneAddX
    rw [west]
    simp
  have evaluation := circleNumerator_eval_stereo
    (initialP0 message) (initialP1 message)
    (initialP0_degree_lt message) (initialP1_degree_lt message)
    (rationalCircleX t) (rationalCircleY t) onCircle notWest
  dsimp only at evaluation
  rw [stereo_rationalCircle t finite] at evaluation
  simpa only [initialCircleValue, circleDenominator] using evaluation

theorem width29Batch_add
    (left right : Fin 29 → K) (gamma : K) :
    width29Batch (fun lane => left lane + right lane) gamma =
      width29Batch left gamma + width29Batch right gamma := by
  unfold width29Batch
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem width29Batch_sub
    (left right : Fin 29 → K) (gamma : K) :
    width29Batch (fun lane => left lane - right lane) gamma =
      width29Batch left gamma - width29Batch right gamma := by
  unfold width29Batch
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem width29Batch_scale
    (values : Fin 29 → K) (gamma scale : K) :
    width29Batch (fun lane => values lane * scale) gamma =
      width29Batch values gamma * scale := by
  unfold width29Batch
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lane _
  ring

theorem twoPointInterpolant_width29
    (t0 t1 : K)
    (a b : Fin 29 → K) (gamma t : K) :
    twoPointInterpolant t0 t1 (width29Batch a gamma)
        (width29Batch b gamma) t =
      width29Batch
        (fun lane => twoPointInterpolant t0 t1 (a lane) (b lane) t)
        gamma := by
  unfold twoPointInterpolant
  calc
    width29Batch a gamma +
        (width29Batch b gamma - width29Batch a gamma) * (t - t0) /
          (t1 - t0) =
      width29Batch a gamma +
        width29Batch (fun lane => b lane - a lane) gamma *
          ((t - t0) / (t1 - t0)) := by
      rw [width29Batch_sub]
      ring
    _ = width29Batch a gamma +
        width29Batch
          (fun lane => (b lane - a lane) * ((t - t0) / (t1 - t0)))
          gamma := by
      rw [width29Batch_scale]
    _ = width29Batch
        (fun lane => a lane +
          (b lane - a lane) * ((t - t0) / (t1 - t0))) gamma := by
      rw [width29Batch_add]
    _ = width29Batch
        (fun lane => a lane + (b lane - a lane) * (t - t0) /
          (t1 - t0)) gamma := by
      congr 1
      funext lane
      ring

/-- Batching and the complete two-point quotient commute.  Consequently the
verifier can derive the quotient at an authenticated opening from the same
29 opened component values and the two public component-evaluation vectors;
there is no algebraic need for a separately authenticated quotient leaf. -/
theorem width29Batch_twoPointDeepQuotient
    (received : Fin 29 → K → K)
    (t0 t1 : K)
    (a b : Fin 29 → K) (gamma t : K)
    (notFirst : t ≠ t0) (notSecond : t ≠ t1) :
    twoPointDeepQuotient
        (fun point => width29Batch (fun lane => received lane point) gamma)
        t0 t1 (width29Batch a gamma) (width29Batch b gamma) t =
      width29Batch
        (fun lane => twoPointDeepQuotient (received lane)
          t0 t1 (a lane) (b lane) t)
        gamma := by
  have zeroFree := twoPointZerofier_ne_zero t0 t1 t notFirst notSecond
  unfold twoPointDeepQuotient
  rw [twoPointInterpolant_width29 t0 t1 a b gamma t]
  unfold width29Batch
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro lane _
  field_simp [zeroFree]

/-! ## Ordinary two-root factorisation and degree drop -/

noncomputable def polynomialTwoPointInterpolant (t0 t1 a b : K) : K[X] :=
  C a + C ((b - a) / (t1 - t0)) * (X - C t0)

noncomputable def polynomialTwoPointZerofier (t0 t1 : K) : K[X] :=
  (X - C t0) * (X - C t1)

theorem polynomialTwoPointInterpolant_eval
    (t0 t1 a b t : K) :
    (polynomialTwoPointInterpolant t0 t1 a b).eval t =
      twoPointInterpolant t0 t1 a b t := by
  simp [polynomialTwoPointInterpolant, twoPointInterpolant]
  ring

theorem polynomialTwoPointZerofier_monic (t0 t1 : K) :
    (polynomialTwoPointZerofier t0 t1).Monic := by
  exact (monic_X_sub_C t0).mul (monic_X_sub_C t1)

theorem polynomialTwoPointZerofier_natDegree (t0 t1 : K) :
    (polynomialTwoPointZerofier t0 t1).natDegree = 2 := by
  rw [polynomialTwoPointZerofier,
    Polynomial.natDegree_mul (X_sub_C_ne_zero t0) (X_sub_C_ne_zero t1)]
  simp

/-- If an ordinary polynomial carries the two claimed evaluations, subtracting
the exact two-point interpolant leaves both distinct linear factors. -/
theorem polynomialTwoPointZerofier_dvd_residual
    (p : K[X]) (t0 t1 a b : K) (distinct : t0 ≠ t1)
    (atFirst : p.eval t0 = a) (atSecond : p.eval t1 = b) :
    polynomialTwoPointZerofier t0 t1 ∣
      p - polynomialTwoPointInterpolant t0 t1 a b := by
  have firstRoot :
      (p - polynomialTwoPointInterpolant t0 t1 a b).IsRoot t0 := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub,
      polynomialTwoPointInterpolant_eval,
      twoPointInterpolant_at_first t0 t1 a b, atFirst, sub_self]
  have secondRoot :
      (p - polynomialTwoPointInterpolant t0 t1 a b).IsRoot t1 := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub,
      polynomialTwoPointInterpolant_eval,
      twoPointInterpolant_at_second t0 t1 a b distinct, atSecond, sub_self]
  have firstDivides : X - C t0 ∣
      p - polynomialTwoPointInterpolant t0 t1 a b :=
    Polynomial.dvd_iff_isRoot.mpr firstRoot
  have secondDivides : X - C t1 ∣
      p - polynomialTwoPointInterpolant t0 t1 a b :=
    Polynomial.dvd_iff_isRoot.mpr secondRoot
  have coprime : IsCoprime (X - C t0 : K[X]) (X - C t1) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr distinct).isUnit
  exact coprime.mul_dvd firstDivides secondDivides

/-- Nonzero exact division by the two-point zerofier removes exactly two
ordinary degrees.  The statement is factorisation-based and avoids unfolding
Mathlib's recursive monic-division implementation. -/
theorem polynomialTwoPointQuotient_degree_drop
    (residual : K[X]) (t0 t1 : K)
    (nonzero : residual ≠ 0)
    (divisible : polynomialTwoPointZerofier t0 t1 ∣ residual) :
    ∃ quotient : K[X],
      residual = polynomialTwoPointZerofier t0 t1 * quotient ∧
      quotient.natDegree + 2 = residual.natDegree := by
  obtain ⟨quotient, factorisation⟩ := divisible
  have zerofierNonzero : polynomialTwoPointZerofier t0 t1 ≠ 0 :=
    (polynomialTwoPointZerofier_monic t0 t1).ne_zero
  have quotientNonzero : quotient ≠ 0 := by
    intro quotientZero
    rw [quotientZero, mul_zero] at factorisation
    exact nonzero factorisation
  refine ⟨quotient, factorisation, ?_⟩
  rw [factorisation, Polynomial.natDegree_mul zerofierNonzero quotientNonzero,
    polynomialTwoPointZerofier_natDegree, Nat.add_comm]

#print axioms rationalCircle_on_circle
#print axioms stereo_rationalCircle
#print axioms rationalCircle_pair_injective
#print axioms twoPointInterpolant_at_first
#print axioms twoPointInterpolant_at_second
#print axioms twoPointZerofier_eq_zero_iff
#print axioms initialCircleValue_width29BatchMessage
#print axioms circleNumerator_eval_initialCircleValue
#print axioms width29Batch_twoPointDeepQuotient
#print axioms polynomialTwoPointZerofier_dvd_residual
#print axioms polynomialTwoPointQuotient_degree_drop

end AspisV8A100TwoPointDeep

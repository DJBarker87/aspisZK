import Mathlib

/-!
# V8-A100 affine-chord quotient in the deployed circle coordinate ring

This file connects the pointwise affine-chord quotient to the exact circle
polynomial representation `p0(X) + Y * p1(X)`, with `Y^2 = 1-X^2`.
It deliberately treats the equal-x and distinct-x secants separately: the
deployed Rust interpolation makes the same coordinate choice.
-/

set_option autoImplicit false

namespace AspisV8A100CircleChordQuotient

open Polynomial

variable {K : Type*} [Field K]

def chordC (x0 y0 x1 y1 : K) : K := x0 * y1 - y0 * x1
def chordU (y0 y1 : K) : K := y0 - y1
def chordV (x0 x1 : K) : K := x1 - x0

noncomputable def chordXPart (x0 y0 x1 y1 : K) : K[X] :=
  C (chordC x0 y0 x1 y1) + C (chordU y0 y1) * X

noncomputable def chordNorm (x0 y0 x1 y1 : K) : K[X] :=
  chordXPart x0 y0 x1 y1 ^ 2 -
    C (chordV x0 x1 ^ 2) * (1 - X ^ 2)

def chordNormLeading (x0 y0 x1 y1 : K) : K :=
  chordU y0 y1 ^ 2 + chordV x0 x1 ^ 2

theorem chord_vanishes_first
    (x0 y0 x1 y1 : K) :
    chordC x0 y0 x1 y1 + chordU y0 y1 * x0 +
      chordV x0 x1 * y0 = 0 := by
  simp only [chordC, chordU, chordV]
  ring

theorem chord_vanishes_second
    (x0 y0 x1 y1 : K) :
    chordC x0 y0 x1 y1 + chordU y0 y1 * x1 +
      chordV x0 x1 * y1 = 0 := by
  simp only [chordC, chordU, chordV]
  ring

/-- The norm of the secant chord is its leading coefficient times the two
distinct x-coordinate factors. -/
theorem chordNorm_factor
    (x0 y0 x1 y1 : K)
    (on0 : x0 ^ 2 + y0 ^ 2 = 1)
    (on1 : x1 ^ 2 + y1 ^ 2 = 1) :
    chordNorm x0 y0 x1 y1 =
      C (chordNormLeading x0 y0 x1 y1) *
        ((X - C x0) * (X - C x1)) := by
  have linearCoefficient :
      2 * chordC x0 y0 x1 y1 * chordU y0 y1 =
        -(chordNormLeading x0 y0 x1 y1 * (x0 + x1)) := by
    simp only [chordC, chordU, chordNormLeading, chordV]
    linear_combination (x0 - x1) * on0 - (x0 - x1) * on1
  have constantCoefficient :
      chordC x0 y0 x1 y1 ^ 2 - chordV x0 x1 ^ 2 =
        chordNormLeading x0 y0 x1 y1 * (x0 * x1) := by
    simp only [chordC, chordU, chordNormLeading, chordV]
    linear_combination
      x1 * (x1 - x0) * on0 + x0 * (x0 - x1) * on1
  have expanded :
      chordNorm x0 y0 x1 y1 =
        C (chordNormLeading x0 y0 x1 y1) * X ^ 2 +
          C (2 * chordC x0 y0 x1 y1 * chordU y0 y1) * X +
          C (chordC x0 y0 x1 y1 ^ 2 - chordV x0 x1 ^ 2) := by
    simp only [chordNorm, chordXPart, chordNormLeading, chordC, chordU,
      chordV, map_sub, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [expanded, linearCoefficient, constantCoefficient]
  simp only [map_neg, map_mul, map_add]
  ring

noncomputable def xZerofier (x0 x1 : K) : K[X] :=
  (X - C x0) * (X - C x1)

noncomputable def conjugateProduct0
    (x0 y0 x1 y1 : K) (r0 r1 : K[X]) : K[X] :=
  chordXPart x0 y0 x1 y1 * r0 -
    C (chordV x0 x1) * (1 - X ^ 2) * r1

noncomputable def conjugateProduct1
    (x0 y0 x1 y1 : K) (r0 r1 : K[X]) : K[X] :=
  chordXPart x0 y0 x1 y1 * r1 - C (chordV x0 x1) * r0

private theorem two_distinct_roots_dvd
    (p : K[X]) (x0 x1 : K) (distinct : x0 ≠ x1)
    (root0 : p.eval x0 = 0) (root1 : p.eval x1 = 0) :
    xZerofier x0 x1 ∣ p := by
  have firstDivides : X - C x0 ∣ p :=
    Polynomial.dvd_iff_isRoot.mpr root0
  have secondDivides : X - C x1 ∣ p :=
    Polynomial.dvd_iff_isRoot.mpr root1
  have coprime : IsCoprime (X - C x0 : K[X]) (X - C x1) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr distinct).isUnit
  exact coprime.mul_dvd firstDivides secondDivides

private theorem conjugateProduct0_root_first
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (on0 : x0 ^ 2 + y0 ^ 2 = 1)
    (residual0 : r0.eval x0 + y0 * r1.eval x0 = 0) :
    (conjugateProduct0 x0 y0 x1 y1 r0 r1).eval x0 = 0 := by
  have chord0 := chord_vanishes_first x0 y0 x1 y1
  simp only [conjugateProduct0, chordXPart, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
  linear_combination
    r0.eval x0 * chord0 - chordV x0 x1 * y0 * residual0 +
      chordV x0 x1 * r1.eval x0 * on0

private theorem conjugateProduct0_root_second
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (on1 : x1 ^ 2 + y1 ^ 2 = 1)
    (residual1 : r0.eval x1 + y1 * r1.eval x1 = 0) :
    (conjugateProduct0 x0 y0 x1 y1 r0 r1).eval x1 = 0 := by
  have chord1 := chord_vanishes_second x0 y0 x1 y1
  simp only [conjugateProduct0, chordXPart, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
  linear_combination
    r0.eval x1 * chord1 - chordV x0 x1 * y1 * residual1 +
      chordV x0 x1 * r1.eval x1 * on1

private theorem conjugateProduct1_root_first
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (residual0 : r0.eval x0 + y0 * r1.eval x0 = 0) :
    (conjugateProduct1 x0 y0 x1 y1 r0 r1).eval x0 = 0 := by
  have chord0 := chord_vanishes_first x0 y0 x1 y1
  simp only [conjugateProduct1, chordXPart, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination r1.eval x0 * chord0 - chordV x0 x1 * residual0

private theorem conjugateProduct1_root_second
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (residual1 : r0.eval x1 + y1 * r1.eval x1 = 0) :
    (conjugateProduct1 x0 y0 x1 y1 r0 r1).eval x1 = 0 := by
  have chord1 := chord_vanishes_second x0 y0 x1 y1
  simp only [conjugateProduct1, chordXPart, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X]
  linear_combination r1.eval x1 * chord1 - chordV x0 x1 * residual1

/-- In the distinct-x case, both components of the residual multiplied by
the conjugate chord carry the two distinct x-coordinate roots. -/
theorem xZerofier_dvd_conjugateProducts
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (on0 : x0 ^ 2 + y0 ^ 2 = 1)
    (on1 : x1 ^ 2 + y1 ^ 2 = 1)
    (distinctX : x0 ≠ x1)
    (residual0 : r0.eval x0 + y0 * r1.eval x0 = 0)
    (residual1 : r0.eval x1 + y1 * r1.eval x1 = 0) :
    xZerofier x0 x1 ∣ conjugateProduct0 x0 y0 x1 y1 r0 r1 ∧
      xZerofier x0 x1 ∣ conjugateProduct1 x0 y0 x1 y1 r0 r1 := by
  constructor
  · exact two_distinct_roots_dvd _ _ _ distinctX
      (conjugateProduct0_root_first x0 y0 x1 y1 r0 r1 on0 residual0)
      (conjugateProduct0_root_second x0 y0 x1 y1 r0 r1 on1 residual1)
  · exact two_distinct_roots_dvd _ _ _ distinctX
      (conjugateProduct1_root_first x0 y0 x1 y1 r0 r1 residual0)
      (conjugateProduct1_root_second x0 y0 x1 y1 r0 r1 residual1)

noncomputable def circleLineMul0
    (x0 y0 x1 y1 : K) (g0 g1 : K[X]) : K[X] :=
  chordXPart x0 y0 x1 y1 * g0 +
    C (chordV x0 x1) * (1 - X ^ 2) * g1

noncomputable def circleLineMul1
    (x0 y0 x1 y1 : K) (g0 g1 : K[X]) : K[X] :=
  C (chordV x0 x1) * g0 + chordXPart x0 y0 x1 y1 * g1

/-- Pair multiplication agrees pointwise with multiplication by the exact
affine chord on the circle `x^2+y^2=1`. -/
theorem circleLineMul_eval
    (x0 y0 x1 y1 x y : K) (g0 g1 : K[X])
    (onCircle : x ^ 2 + y ^ 2 = 1) :
    (circleLineMul0 x0 y0 x1 y1 g0 g1).eval x +
        y * (circleLineMul1 x0 y0 x1 y1 g0 g1).eval x =
      (chordC x0 y0 x1 y1 + chordU y0 y1 * x +
          chordV x0 x1 * y) *
        (g0.eval x + y * g1.eval x) := by
  simp only [circleLineMul0, circleLineMul1, chordXPart,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow]
  have circleRewrite : 1 - x ^ 2 = y ^ 2 := by
    linear_combination -onCircle
  rw [circleRewrite]
  ring

/-- Multiplication by the chord followed by multiplication by its conjugate
is multiplication by the ordinary polynomial `chordNorm`. -/
theorem circleLineMul_conjugateProduct0
    (x0 y0 x1 y1 : K) (r0 r1 : K[X]) :
    circleLineMul0 x0 y0 x1 y1
        (conjugateProduct0 x0 y0 x1 y1 r0 r1)
        (conjugateProduct1 x0 y0 x1 y1 r0 r1) =
      chordNorm x0 y0 x1 y1 * r0 := by
  simp only [circleLineMul0, conjugateProduct0, conjugateProduct1,
    chordNorm, map_pow]
  ring

theorem circleLineMul_conjugateProduct1
    (x0 y0 x1 y1 : K) (r0 r1 : K[X]) :
    circleLineMul1 x0 y0 x1 y1
        (conjugateProduct0 x0 y0 x1 y1 r0 r1)
        (conjugateProduct1 x0 y0 x1 y1 r0 r1) =
      chordNorm x0 y0 x1 y1 * r1 := by
  simp only [circleLineMul1, conjugateProduct0, conjugateProduct1,
    chordNorm, map_pow]
  ring

theorem xZerofier_monic (x0 x1 : K) : (xZerofier x0 x1).Monic := by
  exact (monic_X_sub_C x0).mul (monic_X_sub_C x1)

theorem xZerofier_natDegree (x0 x1 : K) :
    (xZerofier x0 x1).natDegree = 2 := by
  rw [xZerofier, Polynomial.natDegree_mul
    (X_sub_C_ne_zero x0) (X_sub_C_ne_zero x1)]
  simp

private theorem quotient_degree_le
    (p : K[X]) (x0 x1 : K) (bound : Nat)
    (degree : p.natDegree ≤ bound + 2)
    (divisible : xZerofier x0 x1 ∣ p) :
    ∃ q : K[X], p = xZerofier x0 x1 * q ∧ q.natDegree ≤ bound := by
  by_cases zero : p = 0
  · exact ⟨0, by simp only [zero, mul_zero], by simp⟩
  · obtain ⟨q, factor⟩ := divisible
    have zerofierNonzero : xZerofier x0 x1 ≠ 0 :=
      (xZerofier_monic x0 x1).ne_zero
    have quotientNonzero : q ≠ 0 := by
      intro quotientZero
      rw [quotientZero, mul_zero] at factor
      exact zero factor
    have exactDegree : p.natDegree = 2 + q.natDegree := by
      rw [factor, Polynomial.natDegree_mul zerofierNonzero quotientNonzero,
        xZerofier_natDegree]
    refine ⟨q, factor, ?_⟩
    omega

private theorem chordXPart_natDegree_le
    (x0 y0 x1 y1 : K) :
    (chordXPart x0 y0 x1 y1).natDegree ≤ 1 := by
  unfold chordXPart
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))

private theorem one_sub_X_sq_natDegree_le :
    ((1 : K[X]) - X ^ 2).natDegree ≤ 2 := by
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (by simp) (Polynomial.natDegree_pow_le.trans (by simp)))

theorem conjugateProduct0_natDegree_le
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (degree0 : r0.natDegree ≤ 511) (degree1 : r1.natDegree ≤ 511) :
    (conjugateProduct0 x0 y0 x1 y1 r0 r1).natDegree ≤ 513 := by
  have first :
      (chordXPart x0 y0 x1 y1 * r0).natDegree ≤ 512 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (chordXPart_natDegree_le x0 y0 x1 y1) degree0)
  have second :
      (C (chordV x0 x1) * (1 - X ^ 2) * r1).natDegree ≤ 513 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add
        (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (by simp) one_sub_X_sq_natDegree_le)) degree1)
  unfold conjugateProduct0
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le (first.trans (by omega)) second)

theorem conjugateProduct1_natDegree_le
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (degree0 : r0.natDegree ≤ 511) (degree1 : r1.natDegree ≤ 511) :
    (conjugateProduct1 x0 y0 x1 y1 r0 r1).natDegree ≤ 512 := by
  have first :
      (chordXPart x0 y0 x1 y1 * r1).natDegree ≤ 512 := by
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (chordXPart_natDegree_le x0 y0 x1 y1) degree1)
  have second :
      (C (chordV x0 x1) * r0).natDegree ≤ 511 := by
    calc
      (C (chordV x0 x1) * r0).natDegree ≤
          (C (chordV x0 x1)).natDegree + r0.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + 511 := Nat.add_le_add (by simp) degree0
      _ = 511 := by omega
  unfold conjugateProduct1
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le first (second.trans (by omega)))

/-- Constructive distinct-x circle quotient.  A residual of deployed initial
degree `(≤511,≤511)` that vanishes at both points is exactly the chord times
a circle polynomial of degree `(≤511,≤510)`.  This is the one-circle-degree
drop required before applying the existing first fold. -/
theorem distinctX_circleChord_quotient_exists
    (x0 y0 x1 y1 : K) (r0 r1 : K[X])
    (on0 : x0 ^ 2 + y0 ^ 2 = 1)
    (on1 : x1 ^ 2 + y1 ^ 2 = 1)
    (distinctX : x0 ≠ x1)
    (normNonzero : chordNormLeading x0 y0 x1 y1 ≠ 0)
    (degree0 : r0.natDegree ≤ 511) (degree1 : r1.natDegree ≤ 511)
    (residual0 : r0.eval x0 + y0 * r1.eval x0 = 0)
    (residual1 : r0.eval x1 + y1 * r1.eval x1 = 0) :
    ∃ g0 g1 : K[X],
      circleLineMul0 x0 y0 x1 y1 g0 g1 = r0 ∧
      circleLineMul1 x0 y0 x1 y1 g0 g1 = r1 ∧
      g0.natDegree ≤ 511 ∧ g1.natDegree ≤ 510 := by
  obtain ⟨divides0, divides1⟩ := xZerofier_dvd_conjugateProducts
    x0 y0 x1 y1 r0 r1 on0 on1 distinctX residual0 residual1
  obtain ⟨q0, factor0, q0Degree⟩ := quotient_degree_le
    (conjugateProduct0 x0 y0 x1 y1 r0 r1) x0 x1 511
    (by simpa using (conjugateProduct0_natDegree_le
      x0 y0 x1 y1 r0 r1 degree0 degree1)) divides0
  obtain ⟨q1, factor1, q1Degree⟩ := quotient_degree_le
    (conjugateProduct1 x0 y0 x1 y1 r0 r1) x0 x1 510
    (by simpa using (conjugateProduct1_natDegree_le
      x0 y0 x1 y1 r0 r1 degree0 degree1)) divides1
  let k := chordNormLeading x0 y0 x1 y1
  let g0 := C k⁻¹ * q0
  let g1 := C k⁻¹ * q1
  have zerofierNonzero : xZerofier x0 x1 ≠ 0 :=
    (xZerofier_monic x0 x1).ne_zero
  have qIdentity0 :
      chordXPart x0 y0 x1 y1 * q0 +
          C (chordV x0 x1) * (1 - X ^ 2) * q1 = C k * r0 := by
    apply mul_left_cancel₀ zerofierNonzero
    calc
      xZerofier x0 x1 *
          (chordXPart x0 y0 x1 y1 * q0 +
            C (chordV x0 x1) * (1 - X ^ 2) * q1) =
        circleLineMul0 x0 y0 x1 y1
          (conjugateProduct0 x0 y0 x1 y1 r0 r1)
          (conjugateProduct1 x0 y0 x1 y1 r0 r1) := by
            rw [factor0, factor1]
            simp only [circleLineMul0]
            ring
      _ = chordNorm x0 y0 x1 y1 * r0 :=
        circleLineMul_conjugateProduct0 x0 y0 x1 y1 r0 r1
      _ = xZerofier x0 x1 * (C k * r0) := by
        rw [chordNorm_factor x0 y0 x1 y1 on0 on1]
        simp only [xZerofier, k]
        ring
  have qIdentity1 :
      C (chordV x0 x1) * q0 +
          chordXPart x0 y0 x1 y1 * q1 = C k * r1 := by
    apply mul_left_cancel₀ zerofierNonzero
    calc
      xZerofier x0 x1 *
          (C (chordV x0 x1) * q0 +
            chordXPart x0 y0 x1 y1 * q1) =
        circleLineMul1 x0 y0 x1 y1
          (conjugateProduct0 x0 y0 x1 y1 r0 r1)
          (conjugateProduct1 x0 y0 x1 y1 r0 r1) := by
            rw [factor0, factor1]
            simp only [circleLineMul1]
            ring
      _ = chordNorm x0 y0 x1 y1 * r1 :=
        circleLineMul_conjugateProduct1 x0 y0 x1 y1 r0 r1
      _ = xZerofier x0 x1 * (C k * r1) := by
        rw [chordNorm_factor x0 y0 x1 y1 on0 on1]
        simp only [xZerofier, k]
        ring
  have inverseCancel : C k⁻¹ * C k = (1 : K[X]) := by
    rw [← map_mul]
    simp [k, normNonzero]
  refine ⟨g0, g1, ?_, ?_, ?_, ?_⟩
  · change circleLineMul0 x0 y0 x1 y1 (C k⁻¹ * q0) (C k⁻¹ * q1) = r0
    rw [show circleLineMul0 x0 y0 x1 y1 (C k⁻¹ * q0) (C k⁻¹ * q1) =
        C k⁻¹ * (chordXPart x0 y0 x1 y1 * q0 +
          C (chordV x0 x1) * (1 - X ^ 2) * q1) by
      simp only [circleLineMul0]; ring, qIdentity0]
    calc
      C k⁻¹ * (C k * r0) = (C k⁻¹ * C k) * r0 := by ring
      _ = r0 := by rw [inverseCancel]; simp
  · change circleLineMul1 x0 y0 x1 y1 (C k⁻¹ * q0) (C k⁻¹ * q1) = r1
    rw [show circleLineMul1 x0 y0 x1 y1 (C k⁻¹ * q0) (C k⁻¹ * q1) =
        C k⁻¹ * (C (chordV x0 x1) * q0 +
          chordXPart x0 y0 x1 y1 * q1) by
      simp only [circleLineMul1]; ring, qIdentity1]
    calc
      C k⁻¹ * (C k * r1) = (C k⁻¹ * C k) * r1 := by ring
      _ = r1 := by rw [inverseCancel]; simp
  · change (C k⁻¹ * q0).natDegree ≤ 511
    calc
      (C k⁻¹ * q0).natDegree ≤ (C k⁻¹).natDegree + q0.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 0 + q0.natDegree := by rw [Polynomial.natDegree_C]
      _ ≤ 0 + 511 := Nat.add_le_add_left q0Degree 0
      _ = 511 := by omega
  · change (C k⁻¹ * q1).natDegree ≤ 510
    calc
      (C k⁻¹ * q1).natDegree ≤ (C k⁻¹).natDegree + q1.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 0 + q1.natDegree := by rw [Polynomial.natDegree_C]
      _ ≤ 0 + 510 := Nat.add_le_add_left q1Degree 0
      _ = 510 := by omega

noncomputable def linearXZerofier (x : K) : K[X] := X - C x

private theorem linear_quotient_degree_le
    (p : K[X]) (x : K) (bound : Nat)
    (degree : p.natDegree ≤ bound + 1)
    (divisible : linearXZerofier x ∣ p) :
    ∃ q : K[X], p = linearXZerofier x * q ∧ q.natDegree ≤ bound := by
  by_cases zero : p = 0
  · exact ⟨0, by simp only [zero, mul_zero], by simp⟩
  · obtain ⟨q, factor⟩ := divisible
    have zerofierNonzero : linearXZerofier x ≠ 0 := X_sub_C_ne_zero x
    have quotientNonzero : q ≠ 0 := by
      intro quotientZero
      rw [quotientZero, mul_zero] at factor
      exact zero factor
    have exactDegree : p.natDegree = 1 + q.natDegree := by
      rw [factor, Polynomial.natDegree_mul zerofierNonzero quotientNonzero,
        linearXZerofier]
      simp
    refine ⟨q, factor, ?_⟩
    omega

/-- Equal-x secants are not omitted.  Distinct endpoints then have distinct
y coordinates; both residual components carry the common linear x factor,
and division by the chord lowers each component degree by one. -/
theorem equalX_circleChord_quotient_exists
    (x y0 y1 : K) (r0 r1 : K[X])
    (distinctY : y0 ≠ y1)
    (degree0 : r0.natDegree ≤ 511) (degree1 : r1.natDegree ≤ 511)
    (residual0 : r0.eval x + y0 * r1.eval x = 0)
    (residual1 : r0.eval x + y1 * r1.eval x = 0) :
    ∃ g0 g1 : K[X],
      circleLineMul0 x y0 x y1 g0 g1 = r0 ∧
      circleLineMul1 x y0 x y1 g0 g1 = r1 ∧
      g0.natDegree ≤ 510 ∧ g1.natDegree ≤ 510 := by
  have uNonzero : chordU y0 y1 ≠ 0 := sub_ne_zero.mpr distinctY
  have r1Root : r1.eval x = 0 := by
    apply mul_left_cancel₀ uNonzero
    simp only [chordU]
    linear_combination residual0 - residual1
  have r0Root : r0.eval x = 0 := by
    linear_combination residual0 - y0 * r1Root
  have r0Divides : linearXZerofier x ∣ r0 :=
    Polynomial.dvd_iff_isRoot.mpr r0Root
  have r1Divides : linearXZerofier x ∣ r1 :=
    Polynomial.dvd_iff_isRoot.mpr r1Root
  obtain ⟨q0, factor0, q0Degree⟩ := linear_quotient_degree_le
    r0 x 510 (by simpa using degree0) r0Divides
  obtain ⟨q1, factor1, q1Degree⟩ := linear_quotient_degree_le
    r1 x 510 (by simpa using degree1) r1Divides
  let u := chordU y0 y1
  let g0 := C u⁻¹ * q0
  let g1 := C u⁻¹ * q1
  have chordX : chordXPart x y0 x y1 = C u * linearXZerofier x := by
    simp only [chordXPart, chordC, chordU, linearXZerofier, u, map_sub,
      map_mul]
    ring
  have inverseCancel : C u⁻¹ * C u = (1 : K[X]) := by
    rw [← map_mul]
    simp [u, uNonzero]
  refine ⟨g0, g1, ?_, ?_, ?_, ?_⟩
  · change circleLineMul0 x y0 x y1 (C u⁻¹ * q0) (C u⁻¹ * q1) = r0
    simp only [circleLineMul0, chordV, sub_self, map_zero, zero_mul,
      add_zero, chordX]
    calc
      C u * linearXZerofier x * (C u⁻¹ * q0) =
          (C u⁻¹ * C u) * (linearXZerofier x * q0) := by ring
      _ = r0 := by rw [inverseCancel]; simpa using factor0.symm
  · change circleLineMul1 x y0 x y1 (C u⁻¹ * q0) (C u⁻¹ * q1) = r1
    simp only [circleLineMul1, chordV, sub_self, map_zero, zero_mul,
      zero_add, chordX]
    calc
      C u * linearXZerofier x * (C u⁻¹ * q1) =
          (C u⁻¹ * C u) * (linearXZerofier x * q1) := by ring
      _ = r1 := by rw [inverseCancel]; simpa using factor1.symm
  · change (C u⁻¹ * q0).natDegree ≤ 510
    calc
      (C u⁻¹ * q0).natDegree ≤ (C u⁻¹).natDegree + q0.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 0 + q0.natDegree := by rw [Polynomial.natDegree_C]
      _ ≤ 0 + 510 := Nat.add_le_add_left q0Degree 0
      _ = 510 := by omega
  · change (C u⁻¹ * q1).natDegree ≤ 510
    calc
      (C u⁻¹ * q1).natDegree ≤ (C u⁻¹).natDegree + q1.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 0 + q1.natDegree := by rw [Polynomial.natDegree_C]
      _ ≤ 0 + 510 := Nat.add_le_add_left q1Degree 0
      _ = 510 := by omega

#print axioms chordNorm_factor
#print axioms xZerofier_dvd_conjugateProducts
#print axioms distinctX_circleChord_quotient_exists
#print axioms circleLineMul_eval
#print axioms equalX_circleChord_quotient_exists

end AspisV8A100CircleChordQuotient

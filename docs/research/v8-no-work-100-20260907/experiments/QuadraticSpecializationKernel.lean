import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Ring

/-!
The actual polynomial map behind the square-specialization multiplicity.
Mathlib orders the Sylvester input as (p,q) and maps it to f*q+f'*p.
Thus the kernel pair here is (s*V,-2*s*V'), not the reversed pair.
No characteristic-zero assumption is needed for these identities or bounds.
Separability/nonzero resultant is a separate later prerequisite.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSpecializationKernel
noncomputable section
open Polynomial

/-- Every root of the literal quadratic gives the discriminant square.
The root may be chosen adaptively; this is not a fixed-target root count. -/
theorem discriminant_square_of_root
    {R : Type*} [CommRing R] (a b c u : R)
    (root : a * u ^ 2 + b * u + c = 0) :
    b ^ 2 - 4 * a * c = (2 * a * u + b) ^ 2 := by
  have identity : (2 * a * u + b) ^ 2 =
      (b ^ 2 - 4 * a * c) + 4 * a * (a * u ^ 2 + b * u + c) := by ring
  rw [root, mul_zero, add_zero] at identity
  exact identity.symm

/-- The second input block has the negative derivative multiplier. -/
def squareKernelPair {K : Type*} [Field K] (V s : K[X]) : K[X] × K[X] :=
  (s * V, Polynomial.C (-2) * s * V.derivative)

theorem square_kernel_identity
    {K : Type*} [Field K] (c : K) (V s : K[X]) :
    (Polynomial.C c * V ^ 2) * (squareKernelPair V s).2 +
      (Polynomial.C c * V ^ 2).derivative * (squareKernelPair V s).1 = 0 := by
  simp only [squareKernelPair, Polynomial.derivative_C_mul,
    Polynomial.derivative_sq, Polynomial.C_neg, Polynomial.C_ofNat]
  ring

theorem square_kernel_pair_injective
    {K : Type*} [Field K] (V : K[X]) (nonzero : V ≠ 0) :
    Function.Injective (squareKernelPair V) := by
  intro s t equal
  have products := congrArg Prod.fst equal
  exact mul_right_cancel₀ nonzero products

theorem square_kernel_pair_add
    {K : Type*} [Field K] (V s t : K[X]) :
    squareKernelPair V (s + t) = squareKernelPair V s + squareKernelPair V t := by
  apply Prod.ext
  · change (s + t) * V = s * V + t * V
    ring
  · change Polynomial.C (-2) * (s + t) * V.derivative =
      Polynomial.C (-2) * s * V.derivative + Polynomial.C (-2) * t * V.derivative
    ring

theorem square_kernel_pair_smul
    {K : Type*} [Field K] (V s : K[X]) (c : K) :
    squareKernelPair V (c • s) = c • squareKernelPair V s := by
  apply Prod.ext
  · change (c • s) * V = c • (s * V)
    simp only [Polynomial.smul_eq_C_mul]
    ring
  · change Polynomial.C (-2) * (c • s) * V.derivative =
      c • (Polynomial.C (-2) * s * V.derivative)
    simp only [Polynomial.smul_eq_C_mul]
    ring

/-- The two literal blocks fit the Sylvester coefficient spaces for a
degree-2m polynomial and its degree-at-most-(2m-1) derivative. -/
theorem square_kernel_pair_degree
    {K : Type*} [Field K] (V s : K[X]) (m : Nat)
    (positive : 0 < m) (vDegree : V.natDegree ≤ m) (sDegree : s.natDegree < m) :
    (squareKernelPair V s).1.natDegree < 2 * m ∧
      (squareKernelPair V s).2.natDegree < 2 * m - 1 := by
  have firstBound : (s * V).natDegree ≤ s.natDegree + V.natDegree :=
    Polynomial.natDegree_mul_le
  have derivativeBound : V.derivative.natDegree ≤ m - 1 :=
    (Polynomial.natDegree_derivative_le V).trans (Nat.sub_le_sub_right vDegree 1)
  have scaledBound : (Polynomial.C (-2 : K) * s).natDegree ≤ s.natDegree := by
    simpa only [Polynomial.natDegree_C, zero_add] using
      (Polynomial.natDegree_mul_le (p := Polynomial.C (-2 : K)) (q := s))
  have secondBound : (Polynomial.C (-2 : K) * s * V.derivative).natDegree ≤
      (Polynomial.C (-2 : K) * s).natDegree + V.derivative.natDegree :=
    Polynomial.natDegree_mul_le
  change (s * V).natDegree < 2 * m ∧
    (Polynomial.C (-2 : K) * s * V.derivative).natDegree < 2 * m - 1
  constructor <;> omega

theorem square_degree_bounds
    {K : Type*} [Field K] (c : K) (V : K[X]) (m : Nat)
    (vDegree : V.natDegree ≤ m) :
    (Polynomial.C c * V ^ 2).natDegree ≤ 2 * m ∧
      (Polynomial.C c * V ^ 2).derivative.natDegree ≤ 2 * m - 1 := by
  have squareBound : (Polynomial.C c * V ^ 2).natDegree ≤ 2 * m := by
    have mulBound := Polynomial.natDegree_mul_le
      (p := Polynomial.C c) (q := V ^ 2)
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_pow, zero_add] at mulBound
    omega
  exact ⟨squareBound, (Polynomial.natDegree_derivative_le _).trans
    (Nat.sub_le_sub_right squareBound 1)⟩

/-- No assumed matrix/source correspondence: this is the literal
`Polynomial.sylvesterMap` with its real ordering and degree-space bounds.
The supplied s need not be a monomial or an honestly generated polynomial. -/
theorem actual_sylvester_map_zero
    {K : Type*} [Field K] (c : K) (V s : K[X]) (m : Nat)
    (positive : 0 < m) (vDegree : V.natDegree ≤ m) (sDegree : s.natDegree < m) :
    Polynomial.sylvesterMap (Polynomial.C c * V ^ 2)
      (Polynomial.C c * V ^ 2).derivative
      (square_degree_bounds c V m vDegree).1
      (square_degree_bounds c V m vDegree).2
      (⟨(squareKernelPair V s).1, Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt
          (Nat.cast_lt.mpr (square_kernel_pair_degree V s m positive vDegree sDegree).1))⟩,
       ⟨(squareKernelPair V s).2, Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt
          (Nat.cast_lt.mpr (square_kernel_pair_degree V s m positive vDegree sDegree).2))⟩) = 0 := by
  apply Subtype.ext
  exact square_kernel_identity c V s

#print axioms discriminant_square_of_root
#print axioms square_kernel_identity
#print axioms square_kernel_pair_injective
#print axioms square_kernel_pair_add
#print axioms square_kernel_pair_smul
#print axioms square_kernel_pair_degree
#print axioms square_degree_bounds
#print axioms actual_sylvester_map_zero

end
end AspisV8.QuadraticSpecializationKernel

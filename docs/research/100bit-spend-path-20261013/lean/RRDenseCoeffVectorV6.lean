import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.Polynomial.Taylor

open Polynomial
noncomputable section
namespace RRDenseCoeffVector
variable {K : Type*} [Field K]

def coeffAt (cs : List K) (i : Nat) : K := (cs[i]?).getD 0

def toPolynomial (cs : List K) : K[X] :=
  ∑ i ∈ Finset.range cs.length, Polynomial.monomial i (coeffAt cs i)

def taylorCoeffVector (cs : List K) (a : K) (j : Nat) : K :=
  ∑ i ∈ Finset.range cs.length,
    if j ≤ i then (i.choose j : K) * coeffAt cs i * a ^ (i - j) else 0

theorem coeff_toPolynomial (cs : List K) (n : Nat) :
    (toPolynomial cs).coeff n = coeffAt cs n := by
  classical
  unfold toPolynomial coeffAt
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hne
    simp [Polynomial.coeff_monomial, hne]
  · intro hn
    have hnle : cs.length ≤ n := by
      simp only [Finset.mem_range] at hn
      omega
    rw [List.getElem?_eq_none hnle]
    simp

theorem taylor_coeff_toPolynomial (cs : List K) (a : K) (j : Nat) :
    (Polynomial.taylor a (toPolynomial cs)).coeff j = taylorCoeffVector cs a j := by
  classical
  unfold toPolynomial taylorCoeffVector
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.taylor_monomial]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  by_cases hij : j ≤ i
  · simp [hij, mul_comm, mul_left_comm, mul_assoc]
  · have hchoose : i.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hij, hchoose]

#eval (0 : ZMod 3)
#print axioms taylor_coeff_toPolynomial
end RRDenseCoeffVector

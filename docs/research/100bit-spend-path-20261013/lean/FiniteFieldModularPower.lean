import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.BinaryRec

open Polynomial
noncomputable section

universe u
variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]

def polynomialModPower (a m : K[X]) : Nat → K[X] :=
  Nat.binaryRec 1 (fun b _ z => (z * z * (if b then a else 1)) %ₘ m)

theorem polynomialModPower_congruent (a m : K[X]) (hm : m.Monic)
    (hdeg : (0 : WithBot Nat) < degree m) (n : Nat) :
    m ∣ polynomialModPower a m n - a ^ n := by
  refine Nat.binaryRec (motive := fun k => m ∣ polynomialModPower a m k - a ^ k) ?_ ?_ n
  · simp [polynomialModPower]
  · intro b n ih
    change m ∣
      (Nat.binaryRec 1 (fun b _ z => (z * z * (if b then a else 1)) %ₘ m)
        (Nat.bit b n)) - a ^ Nat.bit b n
    have hbase :
        (fun b _ z => (z * z * (if b then a else 1)) %ₘ m) false 0 1 = 1 := by
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul]
      rw [(Polynomial.modByMonic_eq_self_iff hm).2 ?_]
      simpa using hdeg
    rw [Nat.binaryRec_eq b n (Or.inl hbase)]
    have hpow : a ^ Nat.bit b n = a ^ n * a ^ n * (if b then a else 1) := by
      calc
        a ^ Nat.bit b n = a ^ (2 * n + b.toNat) := by rw [Nat.bit_val]
        _ = a ^ n * a ^ n * (if b then a else 1) := by
          cases b <;> simp [pow_add, pow_mul, mul_pow, pow_two, Nat.mul_comm] <;> ring
    have hprod : m ∣
        polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1) -
          (a ^ n * a ^ n * (if b then a else 1)) := by
      have hfac :
          polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1) -
            (a ^ n * a ^ n * (if b then a else 1)) =
            (polynomialModPower a m n - a ^ n) *
              ((polynomialModPower a m n + a ^ n) * (if b then a else 1)) := by ring
      rw [hfac]
      exact dvd_mul_of_dvd_left ih _
    have hmod : m ∣
        (polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) %ₘ m -
          (polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) :=
      Polynomial.dvd_modByMonic_sub _ _
    have htotal : m ∣
        ((polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) %ₘ m) -
          a ^ Nat.bit b n := by
      rw [hpow]
      have hsum :
          ((polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) %ₘ m) -
            (polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) +
            ((polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) -
              (a ^ n * a ^ n * (if b then a else 1))) =
          ((polynomialModPower a m n * polynomialModPower a m n * (if b then a else 1)) %ₘ m) -
            (a ^ n * a ^ n * (if b then a else 1)) := by ring
      rw [← hsum]
      exact dvd_add hmod hprod
    simpa [polynomialModPower] using htotal

theorem polynomialModPower_remainder (a m : K[X]) (hm : m.Monic)
    (hdeg : (0 : WithBot Nat) < degree m) (n : Nat) :
    polynomialModPower a m n %ₘ m = a ^ n %ₘ m := by
  apply Polynomial.modByMonic_eq_of_dvd_sub hm
  exact polynomialModPower_congruent a m hm hdeg n

#print axioms polynomialModPower_congruent
#print axioms polynomialModPower_remainder

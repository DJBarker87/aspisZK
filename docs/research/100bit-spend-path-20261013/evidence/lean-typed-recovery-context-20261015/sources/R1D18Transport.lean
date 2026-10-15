import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! The natural-number arithmetic model of the R1 D18 digit permutation.
This file says nothing about the Rust bitwise implementation or semantic
correspondence. -/

set_option autoImplicit false

namespace AspisR1

/-- Five base-four digits reordered by τ = [3,4,2,0,1]. -/
def rowNat (j : Nat) : Nat :=
  64 * (j % 4) + 256 * ((j / 4) % 4) + 16 * ((j / 16) % 4) +
    ((j / 64) % 4) + 4 * ((j / 256) % 4)

theorem rowNat_lt (j : Nat) : rowNat j < 1024 := by
  have h0 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  have h1 : (j / 4) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h2 : (j / 16) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h3 : (j / 64) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h4 : (j / 256) % 4 < 4 := Nat.mod_lt _ (by omega)
  unfold rowNat
  omega

/-- Reconstruct a number below 4^5 from its five radix-four digits. -/
theorem radix4_reconstruct (j : Nat) (hj : j < 1024) :
    j = j % 4 + 4 * ((j / 4) % 4) + 16 * ((j / 16) % 4) +
      64 * ((j / 64) % 4) + 256 * ((j / 256) % 4) := by
  have h0 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  have h1 : (j / 4) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h2 : (j / 16) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h3 : (j / 64) % 4 < 4 := Nat.mod_lt _ (by omega)
  have h4 : (j / 256) % 4 < 4 := Nat.mod_lt _ (by omega)
  omega

/-- Extract the five digits from a bounded radix-four expansion. The quotient
equations are supplied explicitly so arithmetic automation never has to infer
identities between nested divisions. -/
theorem radix4_digit_extract (n a b c d e : Nat)
    (hexpand : n = a + 4 * b + 16 * c + 64 * d + 256 * e)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) (he : e < 4) :
    n % 4 = a ∧ (n / 4) % 4 = b ∧ (n / 16) % 4 = c ∧
      (n / 64) % 4 = d ∧ (n / 256) % 4 = e := by
  have h0 : n % 4 + 4 * (n / 4) = n := Nat.mod_add_div n 4
  have h1 : (n / 4) % 4 + 4 * ((n / 4) / 4) = n / 4 :=
    Nat.mod_add_div (n / 4) 4
  have h2 : ((n / 4) / 4) % 4 + 4 * (((n / 4) / 4) / 4) = (n / 4) / 4 :=
    Nat.mod_add_div ((n / 4) / 4) 4
  have h3 : (((n / 4) / 4) / 4) % 4 +
      4 * ((((n / 4) / 4) / 4) / 4) = ((n / 4) / 4) / 4 :=
    Nat.mod_add_div (((n / 4) / 4) / 4) 4
  have h4 : ((((n / 4) / 4) / 4) / 4) % 4 +
      4 * (((((n / 4) / 4) / 4) / 4) / 4) = (((n / 4) / 4) / 4) / 4 :=
    Nat.mod_add_div ((((n / 4) / 4) / 4) / 4) 4
  have hmod4 : (n / 16) % 4 = ((n / 4) / 4) % 4 := by
    rw [← Nat.div_div_eq_div_mul n 4 4]
  have hmod64 : (n / 64) % 4 = (((n / 4) / 4) / 4) % 4 := by
    rw [← Nat.div_div_eq_div_mul n 4 16]
    rw [← Nat.div_div_eq_div_mul (n / 4) 4 4]
  have hmod256 : (n / 256) % 4 = ((((n / 4) / 4) / 4) / 4) % 4 := by
    rw [← Nat.div_div_eq_div_mul n 4 64]
    rw [← Nat.div_div_eq_div_mul (n / 4) 4 16]
    rw [← Nat.div_div_eq_div_mul ((n / 4) / 4) 4 4]
  have hfirst : n % 4 = a := by omega
  have hsecond : (n / 4) % 4 = b := by omega
  have hthird : ((n / 4) / 4) % 4 = c := by omega
  have hfourth : (((n / 4) / 4) / 4) % 4 = d := by omega
  have hfifth : ((((n / 4) / 4) / 4) / 4) % 4 = e := by omega
  exact ⟨hfirst, hsecond, hmod4 ▸ hthird, hmod64 ▸ hfourth, hmod256 ▸ hfifth⟩

/-- Output digit 0 is input digit 3. -/
theorem rowNat_digit0 (j : Nat) :
    rowNat j % 4 = (j / 64) % 4 := by
  have hrep : rowNat j = (j / 64) % 4 + 4 * ((j / 256) % 4) +
      16 * ((j / 16) % 4) + 64 * (j % 4) + 256 * ((j / 4) % 4) := by
    unfold rowNat
    omega
  have hx := radix4_digit_extract (rowNat j) ((j / 64) % 4)
    ((j / 256) % 4) ((j / 16) % 4) (j % 4) ((j / 4) % 4) hrep
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))
  exact hx.1

/-- Output digit 1 is input digit 4. -/
theorem rowNat_digit1 (j : Nat) :
    (rowNat j / 4) % 4 = (j / 256) % 4 := by
  have hrep : rowNat j = (j / 64) % 4 + 4 * ((j / 256) % 4) +
      16 * ((j / 16) % 4) + 64 * (j % 4) + 256 * ((j / 4) % 4) := by
    unfold rowNat
    omega
  have hx := radix4_digit_extract (rowNat j) ((j / 64) % 4)
    ((j / 256) % 4) ((j / 16) % 4) (j % 4) ((j / 4) % 4) hrep
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))
  exact hx.2.1

/-- Output digit 2 is input digit 2. -/
theorem rowNat_digit2 (j : Nat) :
    (rowNat j / 16) % 4 = (j / 16) % 4 := by
  have hrep : rowNat j = (j / 64) % 4 + 4 * ((j / 256) % 4) +
      16 * ((j / 16) % 4) + 64 * (j % 4) + 256 * ((j / 4) % 4) := by
    unfold rowNat
    omega
  have hx := radix4_digit_extract (rowNat j) ((j / 64) % 4)
    ((j / 256) % 4) ((j / 16) % 4) (j % 4) ((j / 4) % 4) hrep
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))
  exact hx.2.2.1

/-- Output digit 3 is input digit 0. -/
theorem rowNat_digit3 (j : Nat) :
    (rowNat j / 64) % 4 = j % 4 := by
  have hrep : rowNat j = (j / 64) % 4 + 4 * ((j / 256) % 4) +
      16 * ((j / 16) % 4) + 64 * (j % 4) + 256 * ((j / 4) % 4) := by
    unfold rowNat
    omega
  have hx := radix4_digit_extract (rowNat j) ((j / 64) % 4)
    ((j / 256) % 4) ((j / 16) % 4) (j % 4) ((j / 4) % 4) hrep
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))
  exact hx.2.2.2.1

/-- Output digit 4 is input digit 1. -/
theorem rowNat_digit4 (j : Nat) :
    (rowNat j / 256) % 4 = (j / 4) % 4 := by
  have hrep : rowNat j = (j / 64) % 4 + 4 * ((j / 256) % 4) +
      16 * ((j / 16) % 4) + 64 * (j % 4) + 256 * ((j / 4) % 4) := by
    unfold rowNat
    omega
  have hx := radix4_digit_extract (rowNat j) ((j / 64) % 4)
    ((j / 256) % 4) ((j / 16) % 4) (j % 4) ((j / 4) % 4) hrep
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (Nat.mod_lt _ (by omega))
  exact hx.2.2.2.2

/-- τ is an involution: the digit permutation swaps 0↔3 and 1↔4. -/
theorem rowNat_involutive (j : Nat) (hj : j < 1024) :
    rowNat (rowNat j) = j := by
  have h0 := rowNat_digit0 j
  have h1 := rowNat_digit1 j
  have h2 := rowNat_digit2 j
  have h3 := rowNat_digit3 j
  have h4 := rowNat_digit4 j
  have hrec := radix4_reconstruct j hj
  change 64 * (rowNat j % 4) + 256 * ((rowNat j / 4) % 4) +
      16 * ((rowNat j / 16) % 4) + ((rowNat j / 64) % 4) +
      4 * ((rowNat j / 256) % 4) = j
  rw [h0, h1, h2, h3, h4]
  omega

def row (j : Fin 1024) : Fin 1024 :=
  ⟨rowNat j.val, rowNat_lt j.val⟩

theorem row_involutive (j : Fin 1024) : row (row j) = j := by
  apply Fin.ext
  exact rowNat_involutive j.val j.isLt

/-- The arithmetic row permutation is represented by an equivalence whose
inverse is itself. This is only the natural-number model. -/
def rowEquiv : Fin 1024 ≃ Fin 1024 where
  toFun := row
  invFun := row
  left_inv := row_involutive
  right_inv := row_involutive

#print axioms rowNat_lt
#print axioms radix4_reconstruct
#print axioms rowNat_digit0
#print axioms rowNat_digit1
#print axioms rowNat_digit2
#print axioms rowNat_digit3
#print axioms rowNat_digit4
#print axioms rowNat_involutive
#print axioms row_involutive
#print axioms rowEquiv

end AspisR1

import R1D18Transport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Arithmetic equivalence between the ten binary row factors and the five
radix-four tensor factors. This is a model-level identity only. -/

set_option autoImplicit false

namespace AspisR1

open scoped BigOperators

variable {K : Type} [Field K]

def d18Tau (d : Fin 5) : Fin 5 :=
  ⟨if d.val = 0 then 3 else if d.val = 3 then 0 else
    if d.val = 1 then 4 else if d.val = 4 then 1 else 2,
    by fin_cases d <;> norm_num⟩

theorem d18Tau_involutive (d : Fin 5) : d18Tau (d18Tau d) = d := by
  apply Fin.ext
  fin_cases d <;> norm_num [d18Tau]

def d18BitIndexEquiv : (Fin 5 × Fin 2) ≃ Fin 10 :=
  { toFun := fun x => ⟨x.2.val + 2 * (d18Tau x.1).val, by
      have hu := x.2.isLt
      have ht := (d18Tau x.1).isLt
      omega⟩
    invFun := fun b =>
      (d18Tau ⟨b.val / 2, by have := b.isLt; omega⟩,
        ⟨b.val % 2, Nat.mod_lt _ (by omega)⟩)
    left_inv := by
      rintro ⟨d, u⟩
      apply Prod.ext
      · apply Fin.ext
        have hquot : (u.val + 2 * (d18Tau d).val) / 2 = (d18Tau d).val := by
          have hu := u.isLt
          omega
        change (d18Tau ⟨(u.val + 2 * (d18Tau d).val) / 2, by omega⟩).val = d.val
        have qfin : (⟨(u.val + 2 * (d18Tau d).val) / 2, by omega⟩ : Fin 5) =
            d18Tau d := Fin.ext hquot
        rw [qfin]
        exact congrArg Fin.val (d18Tau_involutive d)
      · apply Fin.ext
        have hu := u.isLt
        change (u.val + 2 * (d18Tau d).val) % 2 = u.val
        omega
    right_inv := by
      intro b
      apply Fin.ext
      have hquot : b.val / 2 < 5 := by have := b.isLt; omega
      change b.val % 2 + 2 *
        (d18Tau (d18Tau ⟨b.val / 2, hquot⟩)).val = b.val
      rw [d18Tau_involutive]
      exact Nat.mod_add_div b.val 2 }

@[simp] theorem d18BitIndexEquiv_val (d : Fin 5) (u : Fin 2) :
    (d18BitIndexEquiv (d, u)).val = u.val + 2 * (d18Tau d).val := rfl

def pairFactor (a b : K) (s : Nat) : K :=
  (if s % 2 = 0 then 1 - a else a) *
    (if s / 2 = 0 then 1 - b else b)

def rowPoint (p : Fin 10 → K) (j : Fin 1024) : K :=
  ∏ b : Fin 10, if rowNat j.val / 2 ^ b.val % 2 = 0 then
    1 - p ⟨9 - b.val, by have := b.isLt; omega⟩
    else p ⟨9 - b.val, by have := b.isLt; omega⟩

def tensorPoint (p : Fin 10 → K) (j : Fin 1024) : K :=
  ∏ d : Fin 5, pairFactor
    (p ⟨9 - 2 * (d18Tau d).val, by have := (d18Tau d).isLt; omega⟩)
    (p ⟨8 - 2 * (d18Tau d).val, by have := (d18Tau d).isLt; omega⟩)
    ((j.val / 4 ^ d.val) % 4)

private theorem mod4_digit_bit (q : Nat) (u : Fin 2) :
    q / 2 ^ u.val % 2 = (q % 4 / 2 ^ u.val) % 2 := by
  fin_cases u
  · norm_num
  · norm_num
    have hsplit : q % 4 + 4 * (q / 4) = q := Nat.mod_add_div q 4
    have hr : q % 4 < 4 := Nat.mod_lt q (by omega)
    omega

private theorem radix4_digit_bit (n k : Nat) (u : Fin 2) :
    n / 2 ^ (2 * k + u.val) % 2 =
      ((n / 4 ^ k) % 4 / 2 ^ u.val) % 2 := by
  have hpow : 2 ^ (2 * k + u.val) = 4 ^ k * 2 ^ u.val := by
    fin_cases u <;> norm_num [pow_add, pow_mul]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  exact mod4_digit_bit (n / 4 ^ k) u

private theorem rowBit_eq_digitBit (j : Nat) (d : Fin 5) (u : Fin 2) :
    rowNat j / 2 ^ (2 * (d18Tau d).val + u.val) % 2 =
      (((j / 4 ^ d.val) % 4) / 2 ^ u.val) % 2 := by
  have hrow := radix4_digit_bit (rowNat j) (d18Tau d).val u
  have hdigit : (rowNat j / 4 ^ (d18Tau d).val) % 4 =
      (j / 4 ^ d.val) % 4 := by
    fin_cases d <;>
      norm_num [d18Tau, rowNat_digit0, rowNat_digit1, rowNat_digit2,
        rowNat_digit3, rowNat_digit4]
  exact hrow.trans (congrArg (fun x : Nat => (x / 2 ^ u.val) % 2) hdigit)

theorem rowPoint_eq_tensorPoint (p : Fin 10 → K) (j : Fin 1024) :
    rowPoint p j = tensorPoint p j := by
  unfold rowPoint tensorPoint
  calc
    (∏ b : Fin 10, if rowNat j.val / 2 ^ b.val % 2 = 0 then
        1 - p ⟨9 - b.val, by have := b.isLt; omega⟩
        else p ⟨9 - b.val, by have := b.isLt; omega⟩) =
      ∏ x : Fin 5 × Fin 2,
        if rowNat j.val / 2 ^ (d18BitIndexEquiv x).val % 2 = 0 then
          1 - p ⟨9 - (d18BitIndexEquiv x).val, by
            have := (d18BitIndexEquiv x).isLt; omega⟩
        else p ⟨9 - (d18BitIndexEquiv x).val, by
          have := (d18BitIndexEquiv x).isLt; omega⟩ := by
            symm
            apply Fintype.prod_equiv d18BitIndexEquiv
            intro x
            rfl
    _ = ∏ d : Fin 5, pairFactor
        (p ⟨9 - 2 * (d18Tau d).val, by have := (d18Tau d).isLt; omega⟩)
        (p ⟨8 - 2 * (d18Tau d).val, by have := (d18Tau d).isLt; omega⟩)
        ((j.val / 4 ^ d.val) % 4) := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro d hd
      rw [Fin.prod_univ_two]
      have hbit0 := rowBit_eq_digitBit j.val d 0
      have hbit1 := rowBit_eq_digitBit j.val d 1
      simp only [d18BitIndexEquiv_val, Fin.val_zero, Fin.val_one,
        Nat.zero_add] at ⊢
      have hbit0' : rowNat j.val / 2 ^ (2 * (d18Tau d).val) % 2 =
          ((j.val / 4 ^ d.val) % 4) % 2 := by
        simpa using hbit0
      have hbit1' : rowNat j.val / 2 ^ (1 + 2 * (d18Tau d).val) % 2 =
          ((j.val / 4 ^ d.val) % 4 / 2) % 2 := by
        simpa [Nat.add_comm] using hbit1
      rw [hbit0', hbit1']
      have hp1 : (⟨9 - (1 + 2 * (d18Tau d).val), by
          have := (d18Tau d).isLt; omega⟩ : Fin 10) =
          ⟨8 - 2 * (d18Tau d).val, by have := (d18Tau d).isLt; omega⟩ := by
        have ht := (d18Tau d).isLt
        apply Fin.ext
        change 9 - (1 + 2 * (d18Tau d).val) = 8 - 2 * (d18Tau d).val
        omega
      rw [hp1]
      simp only [pairFactor]
      have hslt : ((j.val / 4 ^ d.val) % 4) < 4 := Nat.mod_lt _ (by omega)
      have hhalf : ((j.val / 4 ^ d.val) % 4) / 2 < 2 := by omega
      rw [Nat.mod_eq_of_lt hhalf]

#print axioms d18Tau_involutive
#print axioms rowBit_eq_digitBit
#print axioms rowPoint_eq_tensorPoint

end AspisR1

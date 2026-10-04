import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Integer-only facts for the selected query-root exponent coset.
    This file does not prove the source generator/group correspondence. -/

namespace AspisV8R19.R689SelectedRootExponents

abbrev QN : Nat := 2^18
abbrev M : Nat := 2^31
abbrev C : Nat := 2^13
abbrev B : Nat := 2^11

def exponent (n : Fin QN) : Nat := B + C * n.val

private abbrev E (n : Nat) : Nat := B + C * n

theorem exponent_lt_order (n : Fin QN) : exponent n < M := by
  simp [exponent, B, C, QN, M]
  omega

theorem exponent_pos (n : Fin QN) : 0 < exponent n := by
  simp [exponent, B, C]
  omega

theorem exponent_bounds (n : Fin QN) : 0 < exponent n ∧ exponent n < M :=
  ⟨exponent_pos n, exponent_lt_order n⟩

theorem exponent_injective {i j : Fin QN} (h : exponent i = exponent j) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp [exponent, B, C] at h
  omega

theorem exponent_sum_mod_ne_zero (i j : Fin QN) :
    (exponent i + exponent j) % M ≠ 0 := by
  intro h
  have hdiv : M ∣ exponent i + exponent j := Nat.dvd_of_mod_eq_zero h
  rcases hdiv with ⟨k, hk⟩
  have hi := i.isLt
  have hj := j.isLt
  simp [exponent, B, C, QN, M] at hk
  omega

theorem exponent_residue_nonzero (i : Fin QN) :
    (E i.val : ZMod M) ≠ 0 := by
  intro h
  have hdiv : M ∣ exponent i := (ZMod.natCast_eq_zero_iff _ _).mp h
  rcases hdiv with ⟨k, hk⟩
  have hb := exponent_pos i
  have hu := exponent_lt_order i
  simp [exponent, B, C, QN, M] at hk
  omega

theorem exponent_residue_eq_iff {i j : Fin QN} :
    (exponent i : ZMod M) = exponent j ↔ i = j := by
  constructor
  · intro h
    apply exponent_injective
    have hi := exponent_lt_order i
    have hj := exponent_lt_order j
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hv
  · rintro rfl
    rfl

theorem exponent_residue_ne_neg {i j : Fin QN} :
    (exponent i : ZMod M) ≠ -(exponent j : ZMod M) := by
  intro h
  have hsum : (exponent i : ZMod M) + (exponent j : ZMod M) = 0 := by
    rw [h]
    simp
  rw [← Nat.cast_add] at hsum
  have hdiv : M ∣ exponent i + exponent j :=
    (ZMod.natCast_eq_zero_iff _ _).mp hsum
  rcases hdiv with ⟨k, hk⟩
  simp [exponent, B, C, QN, M] at hk
  omega

#print axioms exponent_bounds
#print axioms exponent_injective
#print axioms exponent_sum_mod_ne_zero
#print axioms exponent_residue_nonzero
#print axioms exponent_residue_eq_iff
#print axioms exponent_residue_ne_neg

end AspisV8R19.R689SelectedRootExponents

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Omega

/-! Integer-only facts for the selected query-root exponent coset.
    This file does not prove the source generator/group correspondence. -/

namespace R689SelectedRootExponents

abbrev QN : Nat := 2^18
abbrev M : Nat := 2^31
abbrev C : Nat := 2^13
abbrev B : Nat := 2^11

def E (n : Nat) : Nat := B + C * n

theorem exponent_bounds (n : Fin QN) : 0 < E n.val ∧ E n.val < M := by
  constructor <;> simp [E, B, C, QN, M] at * <;> omega

theorem exponent_injective {i j : Fin QN} (h : E i.val = E j.val) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  simp [E, B, C] at h
  omega

theorem exponent_residue_nonzero (i : Fin QN) :
    (E i.val : ZMod M) ≠ 0 := by
  intro h
  have hlt := (exponent_bounds i).2
  have hv := congrArg ZMod.val h
  simp only [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
  omega

theorem exponent_residue_eq_iff {i j : Fin QN} :
    (E i.val : ZMod M) = E j.val ↔ i = j := by
  constructor
  · intro h
    apply exponent_injective
    have hi := (exponent_bounds i).2
    have hj := (exponent_bounds j).2
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hv
  · rintro rfl
    rfl

theorem exponent_residue_ne_neg {i j : Fin QN} :
    (E i.val : ZMod M) ≠ -(E j.val : ZMod M) := by
  intro h
  have hsum : (E i.val : ZMod M) + (E j.val : ZMod M) = 0 := by
    rw [h]
    simp
  have hi := i.isLt
  have hj := j.isLt
  have hval := congrArg ZMod.val hsum
  have hmod : (E i.val + E j.val) % M = 0 := by
    simpa only [Nat.cast_add, ZMod.val_natCast] using hval
  have hdiv : M ∣ E i.val + E j.val := Nat.dvd_of_mod_eq_zero hmod
  have hM8192 : 8192 ∣ M := by norm_num [M]
  have h8192 : 8192 ∣ E i.val + E j.val := dvd_trans hM8192 hdiv
  rw [E, E, B, C] at h8192
  simp only [QN] at hi hj
  rcases h8192 with ⟨k, hk⟩
  have hsmall : 8192 * (i.val + j.val) < 8192 * 2^19 := by omega
  norm_num [M] at *
  omega

#print axioms exponent_bounds
#print axioms exponent_injective
#print axioms exponent_residue_nonzero
#print axioms exponent_residue_eq_iff
#print axioms exponent_residue_ne_neg

end R689SelectedRootExponents

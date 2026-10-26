import R1Z.PV_CB3_MachinePass
import R1Z.PV_CB3_DigitSequence
namespace R1Z.PV_CB3_MachineDigits
open PV_CB3_SamplerWord PV_CB3_MachinePass
set_option autoImplicit false

def split : Nat → List (BitVec 32) → List (BitVec 32) × List (BitVec 32)
  | 0, words => ([], words)
  | n + 1, words =>
    let first := passLE words
    let rest := split n first.1
    (first.2.setWidth 32 :: rest.1, rest.2)

theorem remainder_cast (words : List (BitVec 32)) :
    ((passLE words).2.setWidth 32).toNat = (passLE words).2.toNat := by
  have h := remainder_canonical words
  have hb : base < radix := by unfold base radix; omega
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h hb)

/-- The typed repeated division has exactly the same digit and high-word
vectors as the mathematical recurrence, for every count and input vector. -/
theorem projection (n : Nat) (words : List (BitVec 32)) :
    (split n words).1.map BitVec.toNat =
      (PV_CB3_DigitSequence.splitDigits base radix n (words.map BitVec.toNat)).1 ∧
    (split n words).2.map BitVec.toNat =
      (PV_CB3_DigitSequence.splitDigits base radix n (words.map BitVec.toNat)).2 := by
  induction n generalizing words with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hp := PV_CB3_MachinePass.projection words
    have ht := ih (passLE words).1
    dsimp only [split, PV_CB3_DigitSequence.splitDigits]
    simp only [List.map_cons]
    rw [remainder_cast, ht.1, ht.2, hp.1, hp.2]
    exact ⟨rfl, rfl⟩

theorem canonical (n : Nat) (words : List (BitVec 32)) :
    ∀ d, d ∈ (split n words).1 → d.toNat < base := by
  intro d hd
  have hp := (projection n words).1
  have hm : d.toNat ∈ (split n words).1.map BitVec.toNat := List.mem_map.mpr ⟨d, hd, rfl⟩
  rw [hp] at hm
  exact PV_CB3_DigitSequence.digits_canonical base radix (by unfold base; omega) n _ _ hm

#print axioms remainder_cast
#print axioms projection
#print axioms canonical
end R1Z.PV_CB3_MachineDigits

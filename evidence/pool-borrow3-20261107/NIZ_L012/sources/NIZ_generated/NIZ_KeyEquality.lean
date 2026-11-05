import NIZ_Memcmp
set_option autoImplicit false
namespace NIZ_KeyEquality

/-- Fixed-key comparator spec used by NIZ_eq; the Rust stub spells out the
32 conjunctions, while this definition leaves the width symbolic. -/
def same (a b : Nat → Nat) (offset : Nat) : Nat → Bool
  | 0 => true
  | n+1 => decide (a offset = b offset) && same a b (offset+1) n

theorem same_iff (a b : Nat → Nat) (offset count : Nat) :
    same a b offset count = true ↔ ∀ i, i < count → a (offset+i) = b (offset+i) := by
  induction count generalizing offset with
  | zero => simp [same]
  | succ n ih =>
    constructor
    · intro h i hi
      have hs : a offset = b offset ∧ same a b (offset+1) n = true := by
        simpa only [same, Bool.and_eq_true_iff, decide_eq_true_eq] using h
      cases i with
      | zero => simpa using hs.1
      | succ i =>
        have hr := (ih (offset+1)).mp hs.2 i (by omega)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
    · intro h
      have first : a offset = b offset := by simpa using h 0 (by omega)
      have rest : same a b (offset+1) n = true := by
        apply (ih (offset+1)).mpr
        intro i hi
        have hr := h (i+1) (by omega)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
      simp [same, first, rest]
#print axioms same_iff

/-- Native byte-step induction discharges the value part of the key comparison
cut once the SAME native key-byte reads/loop are associated. The native/physical
association is not a new hypothesis of a release theorem. -/
theorem memcmp_eq_spec (a b : Nat → Nat) (reply : Nat → Int)
    (law : ∀ i, i < 32 → (reply i = 0 ↔ a i = b i)) :
    (NIZ_Memcmp.run reply 0 32 = 0) ↔ same a b 0 32 = true := by
  rw [NIZ_Memcmp.key32_zero a b reply law, same_iff]
  simp only [Nat.zero_add]
#print axioms memcmp_eq_spec

/-- On the actual fixed32 byte domain, the cut returns exactly byte equality. -/
theorem spec_key_eq (a b : Nat → Nat) :
    same a b 0 32 = true ↔ ∀ i : Fin 32, a i.val = b i.val := by
  rw [same_iff]
  simp only [Nat.zero_add]
  constructor
  · intro h i; exact h i.val i.isLt
  · intro h i hi; exact h ⟨i,hi⟩
#print axioms spec_key_eq
end NIZ_KeyEquality

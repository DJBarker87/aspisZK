import NIZ_Unique
set_option autoImplicit false
namespace NIZ_Memcmp

/-- Short-circuit loop over logged native replies. Native K004/K005 checks the
single-byte zero law; sign and magnitude are unrestricted. This is a host-tool
model, not an extension of Solana RuntimeMemcmp688. -/
def run (reply : Nat → Int) (offset : Nat) : Nat → Int
  | 0 => 0
  | n+1 => let r := reply offset
           if r = 0 then run reply (offset+1) n else r

theorem zero_iff (a b : Nat → Nat) (reply : Nat → Int) (offset count : Nat)
    (law : ∀ i, i < count → (reply (offset+i) = 0 ↔ a (offset+i) = b (offset+i))) :
    run reply offset count = 0 ↔ ∀ i, i < count → a (offset+i) = b (offset+i) := by
  induction count generalizing offset with
  | zero => simp [run]
  | succ n ih =>
    have nextLaw : ∀ i, i < n →
        (reply (offset+1+i) = 0 ↔ a (offset+1+i) = b (offset+1+i)) := by
      intro i hi
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using law (i+1) (by omega)
    constructor
    · intro h i hi
      have first : reply offset = 0 := by
        by_cases eq : reply offset = 0
        · exact eq
        · simp [run, eq] at h
      have rest : run reply (offset+1) n = 0 := by simpa [run, first] using h
      cases i with
      | zero => simpa using (law 0 (by omega)).mp (by simpa using first)
      | succ i =>
        have hr := (ih (offset+1) nextLaw).mp rest i (by omega)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
    · intro all
      have first : reply offset = 0 := by
        have h := (law 0 (by omega)).mpr (all 0 (by omega))
        simpa using h
      have rest : run reply (offset+1) n = 0 := by
        apply (ih (offset+1) nextLaw).mpr
        intro i hi
        have hr := all (i+1) (by omega)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
      simpa [run, first] using rest
#print axioms zero_iff

/-- Symbolic specialization; no concrete 32-byte recurrence is normalized.
The supplied native per-step laws must concern the SAME key-byte observations. -/
theorem key32_zero (a b : Nat → Nat) (reply : Nat → Int)
    (law : ∀ i, i < 32 → (reply i = 0 ↔ a i = b i)) :
    run reply 0 32 = 0 ↔ ∀ i, i < 32 → a i = b i := by
  simpa only [Nat.zero_add] using (zero_iff a b reply 0 32
    (by simpa only [Nat.zero_add] using law))
#print axioms key32_zero
end NIZ_Memcmp

import Port22ARENA_Bump
set_option autoImplicit false
namespace Port22ARENA

def wordInitial (s l c : BitVec 64) : BitVec 64 := if c = 0 then s+l else c
def wordSaturatingSub (x n : BitVec 64) : BitVec 64 := if x < n then 0 else x-n
def wordCandidate (s l c n a : BitVec 64) : BitVec 64 :=
  wordSaturatingSub (wordInitial s l c) n &&& ~~~(a-1)

/-- The literal wrapping subtraction/complement, not a new mask premise. -/
theorem wrapping_mask (a : BitVec 64) (positive : 0 < a.toNat) :
    (~~~(a-1)).toNat = 2^64-a.toNat := by
  rw [BitVec.toNat_not, BitVec.toNat_sub_of_le (by
    change 1 ≤ a.toNat
    omega)]
  change 2^64-1-(a.toNat-1) = 2^64-a.toNat
  omega

theorem saturating_word (x n : BitVec 64) :
    (wordSaturatingSub x n).toNat = x.toNat-n.toNat := by
  unfold wordSaturatingSub
  split
  · have h : x.toNat < n.toNat := by assumption
    change 0 = x.toNat-n.toNat
    omega
  · rw [BitVec.toNat_sub_of_le (by
      change n.toNat ≤ x.toNat
      have h : ¬ x.toNat < n.toNat := by assumption
      omega)]

theorem initial_word (s l c : BitVec 64)
    (noOverflow : s.toNat+l.toNat < 2^64) :
    (wordInitial s l c).toNat = initial s.toNat l.toNat c.toNat := by
  unfold wordInitial initial
  by_cases zero : c = 0
  · subst c
    simp only [↓reduceIte, BitVec.toNat_add]
    exact Nat.mod_eq_of_lt noOverflow
  · have nz : c.toNat ≠ 0 := by
      intro h
      apply zero
      exact BitVec.eq_of_toNat_eq h
    simp only [zero, nz, ↓reduceIte]

/-- Literal word-body to mathematical candidate correspondence. Nothing about
native unsafe memory, ABI, std or deployed artifacts is assumed or concluded. -/
theorem candidate_word (s l c n a : BitVec 64)
    (noOverflow : s.toNat+l.toNat < 2^64) (positive : 0 < a.toNat) :
    (wordCandidate s l c n a).toNat =
      candidate s.toNat l.toNat c.toNat n.toNat a.toNat := by
  simp only [wordCandidate, BitVec.toNat_and, saturating_word,
    initial_word s l c noOverflow, wrapping_mask a positive, candidate]

#print axioms wrapping_mask
#print axioms saturating_word
#print axioms initial_word
#print axioms candidate_word
end Port22ARENA

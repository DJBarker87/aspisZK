import AspisV8R19.R481NativeQM31Cell

/-! Exact wrapping-word invariant for r105_parse::fields' fast-path canonical
mask. This proves its arithmetic, not align_to, chunks, pushes, or parsing. -/
set_option autoImplicit false
namespace AspisV8R19.R486ParserCanonicalMask

def step (mask word : BitVec 32) : BitVec 32 :=
  mask ||| (word ||| (word + 1))

def accepted (mask : BitVec 32) : Prop := mask >>> 31 = 0
def canonical (word : BitVec 32) : Prop := word < 2147483647

theorem step_accepted (mask word : BitVec 32) :
    accepted (step mask word) ↔ accepted mask ∧ canonical word := by
  unfold step accepted canonical
  bv_decide

def accumulated (mask : BitVec 32) (words : List (BitVec 32)) : BitVec 32 :=
  words.foldl step mask

theorem accumulated_accepted (mask : BitVec 32) (words : List (BitVec 32)) :
    accepted (accumulated mask words) ↔
      accepted mask ∧ ∀ word ∈ words, canonical word := by
  induction words generalizing mask with
  | nil => simp [accumulated]
  | cons head tail ih =>
      change accepted (accumulated (step mask head) tail) ↔ _
      rw [ih, step_accepted]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

theorem zero_accepted : accepted (0 : BitVec 32) := by decide

theorem complete_mask (words : List (BitVec 32)) :
    accepted (accumulated 0 words) ↔ ∀ word ∈ words, canonical word := by
  rw [accumulated_accepted]
  exact and_iff_right zero_accepted

theorem rejects_prime : ¬ canonical (2147483647 : BitVec 32) := by decide
theorem rejects_high_bit : ¬ canonical (2147483648 : BitVec 32) := by decide
theorem rejects_max : ¬ canonical (4294967295 : BitVec 32) := by decide

#print axioms step
#print axioms step_accepted
#print axioms accumulated_accepted
#print axioms complete_mask
#print axioms rejects_prime
#print axioms rejects_high_bit
#print axioms rejects_max
end AspisV8R19.R486ParserCanonicalMask

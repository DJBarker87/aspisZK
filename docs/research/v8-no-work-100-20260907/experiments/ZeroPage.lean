import Mathlib.Tactic

/- Research algebraic model of zero_page.rs: eight-byte LE words followed by
   the unpadded remainder. This is not an Aeneas translation of Rust/std. -/
namespace AspisV8.ZeroPage

def encodeLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * encodeLE bs

theorem encode_zero (bs : List Nat) :
    encodeLE bs = 0 ↔ ∀ b ∈ bs, b = 0 := by
  induction bs with
  | nil => simp [encodeLE]
  | cons b bs ih => simp [encodeLE, ih]

theorem encode_bound (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    encodeLE bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [encodeLE]
  | cons b bs ih =>
    have h := ih (fun x hx => hb x (by simp [hx]))
    have h0 := hb b (by simp)
    simp only [encodeLE, List.length_cons, pow_succ]
    omega

theorem word_zero (bs : List Nat) (hl : bs.length = 8)
    (hb : ∀ b ∈ bs, b < 256) :
    encodeLE bs % 2^64 = 0 ↔ ∀ b ∈ bs, b = 0 := by
  have h := encode_bound bs hb
  rw [hl] at h
  have e : 256^8 = (2:Nat)^64 := by norm_num
  rw [e] at h
  rw [Nat.mod_eq_of_lt h, encode_zero]

def chunkScan (bs : List Nat) : Bool :=
  if bs.length < 8 then bs.all (· == 0)
  else (encodeLE (bs.take 8) % 2^64 == 0) && chunkScan (bs.drop 8)
termination_by bs.length
decreasing_by simp_wf; omega

theorem scan_correct (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    chunkScan bs = true ↔ ∀ b ∈ bs, b = 0 := by
  rw [chunkScan]
  split
  next h => simp
  next h =>
    have ht : (bs.take 8).length = 8 := by simp; omega
    have hp : ∀ b ∈ bs.take 8, b < 256 :=
      fun b hmem => hb b (List.mem_of_mem_take hmem)
    have hd : ∀ b ∈ bs.drop 8, b < 256 :=
      fun b hmem => hb b (List.mem_of_mem_drop hmem)
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [word_zero _ ht hp, scan_correct _ hd]
    constructor
    · intro ⟨ht, hd⟩ b hmem
      have hsplit : b ∈ bs.take 8 ++ bs.drop 8 := by simpa using hmem
      rcases List.mem_append.mp hsplit with hm | hm
      · exact ht b hm
      · exact hd b hm
    · intro hz
      exact ⟨fun b hm => hz b (List.mem_of_mem_take hm),
        fun b hm => hz b (List.mem_of_mem_drop hm)⟩
termination_by bs.length
decreasing_by simp_wf; omega

theorem bytewise_equivalence (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    chunkScan bs = bs.all (· == 0) := by
  apply Bool.eq_iff_iff.mpr
  simpa using scan_correct bs hb

#print axioms encode_zero
#print axioms encode_bound
#print axioms word_zero
#print axioms scan_correct
#print axioms bytewise_equivalence
end AspisV8.ZeroPage

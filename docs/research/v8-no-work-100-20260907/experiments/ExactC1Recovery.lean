import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! Deterministic exact-code recovery, independent of an honest fixture.
The source fixes the full evaluation matrix E, its 1024-row restriction A,
and computes a left inverse B. This leaf proves the algorithmic completeness
and uniqueness consequences of B*A=1. The actual finite source-matrix check
is Rust evidence, not a kernel certificate or a source translation.
No claim of error correction, payment validity, or acceptance coverage. -/
set_option autoImplicit false
namespace AspisV8.ExactC1Recovery
open Matrix
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I]

def sampled (E : Matrix J I K) (positions : I → J) : Matrix I I K :=
  fun i j => E (positions i) j

def recover (B : Matrix I I K) (positions : I → J) (word : J → K) : I → K :=
  B *ᵥ (fun i => word (positions i))

theorem restrict_encode (E : Matrix J I K) (positions : I → J) (message : I → K) :
    (fun i => (E *ᵥ message) (positions i)) = sampled E positions *ᵥ message := by
  rfl

theorem recover_encode (E : Matrix J I K) (B : Matrix I I K)
    (positions : I → J) (leftInverse : B * sampled E positions = 1)
    (message : I → K) : recover B positions (E *ᵥ message) = message := by
  unfold recover
  rw [restrict_encode, mulVec_mulVec, leftInverse, one_mulVec]

/-- No hypothesised honest message: full-code membership is exactly what
re-encoding the algorithm's recovered coefficients checks. -/
theorem full_check_iff_codeword (E : Matrix J I K) (B : Matrix I I K)
    (positions : I → J) (leftInverse : B * sampled E positions = 1)
    (word : J → K) :
    E *ᵥ recover B positions word = word ↔ ∃ message, E *ᵥ message = word := by
  constructor
  · intro h
    exact ⟨recover B positions word,h⟩
  · rintro ⟨message,rfl⟩
    rw [recover_encode E B positions leftInverse]

theorem unique_message_from_sample (E : Matrix J I K) (B : Matrix I I K)
    (positions : I → J) (leftInverse : B * sampled E positions = 1)
    (m n : I → K)
    (agree : ∀ i, (E *ᵥ m) (positions i) = (E *ᵥ n) (positions i)) : m=n := by
  have hr : recover B positions (E *ᵥ m) = recover B positions (E *ᵥ n) := by
    unfold recover
    rw [funext agree]
  simpa only [recover_encode E B positions leftInverse] using hr

/-- The fixed sample can remain unchanged while an off-sample received value
changes. The decoder then returns the same coefficients, but the whole-word
test necessarily fails. This explains the fibre-256 regression universally. -/
theorem off_sample_change_rejected (E : Matrix J I K) (B : Matrix I I K)
    (positions : I → J) (leftInverse : B * sampled E positions = 1)
    (message : I → K) (word : J → K)
    (agree : ∀ i, word (positions i) = (E *ᵥ message) (positions i))
    (different : word ≠ E *ᵥ message) :
    recover B positions word = message ∧ E *ᵥ recover B positions word ≠ word := by
  have h : recover B positions word = message := by
    unfold recover
    rw [funext agree]
    exact recover_encode E B positions leftInverse message
  exact ⟨h,by rw [h]; exact Ne.symm different⟩

#print axioms recover_encode
#print axioms full_check_iff_codeword
#print axioms unique_message_from_sample
#print axioms off_sample_change_rejected

/-- Two disjoint 256-fibre information windows suffice for one arbitrarily
corrupted complete fibre. The anchor message is not an extractor input.
The theorem supplies the recovery guarantee, not payment-validity premises
or a bound saying every accepted word has at most one bad fibre. -/
theorem two_windows_one_bad_fibre (E : Matrix Nat (Fin 1024) K)
    (B0 B1 : Matrix (Fin 1024) (Fin 1024) K)
    (inv0 : B0 * sampled E (fun i => i.val) = 1)
    (inv1 : B1 * sampled E (fun i => 1024+i.val) = 1)
    (message : Fin 1024 → K) (word : Nat → K) (badFibre : Nat)
    (outside : ∀ j, j/4 ≠ badFibre → word j = (E *ᵥ message) j) :
    recover B0 (fun i => i.val) word = message ∨
      recover B1 (fun i => 1024+i.val) word = message := by
  by_cases early : badFibre < 256
  · right
    have agree : (fun i : Fin 1024 => word (1024+i.val)) =
        fun i : Fin 1024 => (E *ᵥ message) (1024+i.val) := by
      funext i
      exact outside _ (by omega)
    unfold recover
    rw [agree]
    exact recover_encode E B1 (fun i => 1024+i.val) inv1 message
  · left
    have agree : (fun i : Fin 1024 => word i.val) =
        fun i : Fin 1024 => (E *ᵥ message) i.val := by
      funext i
      exact outside _ (by omega)
    unfold recover
    rw [agree]
    exact recover_encode E B0 (fun i => i.val) inv0 message

#print axioms two_windows_one_bad_fibre

/-- One COMMON window recovers every semantic column; this is stronger than
a per-column disjunction permitting inconsistent window choices. -/
theorem two_windows_joint_tuple (E : Matrix Nat (Fin 1024) K)
    (B0 B1 : Matrix (Fin 1024) (Fin 1024) K)
    (inv0 : B0 * sampled E (fun i => i.val) = 1)
    (inv1 : B1 * sampled E (fun i => 1024+i.val) = 1)
    (messages : Fin 16 → Fin 1024 → K) (words : Fin 16 → Nat → K)
    (badFibre : Nat)
    (outside : ∀ col j, j/4 ≠ badFibre → words col j = (E *ᵥ messages col) j) :
    (fun col => recover B0 (fun i => i.val) (words col)) = messages ∨
      (fun col => recover B1 (fun i => 1024+i.val) (words col)) = messages := by
  by_cases early : badFibre < 256
  · right
    funext col
    have agree : (fun i : Fin 1024 => words col (1024+i.val)) =
        fun i : Fin 1024 => (E *ᵥ messages col) (1024+i.val) := by
      funext i
      exact outside col _ (by omega)
    unfold recover
    rw [agree]
    exact recover_encode E B1 (fun i => 1024+i.val) inv1 (messages col)
  · left
    funext col
    have agree : (fun i : Fin 1024 => words col i.val) =
        fun i : Fin 1024 => (E *ᵥ messages col) i.val := by
      funext i
      exact outside col _ (by omega)
    unfold recover
    rw [agree]
    exact recover_encode E B0 (fun i => i.val) inv0 (messages col)

#print axioms two_windows_joint_tuple
end AspisV8.ExactC1Recovery

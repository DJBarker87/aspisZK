import S7OwnedP6LoopSimulation
import Mathlib.Data.List.OfFn

/-! S8 traversal invariants. These contracts expose the source-step join;
no bounded Kani comparison is silently promoted to an unbounded Rust proof. -/
set_option autoImplicit false
namespace S8OwnedP6LoopContracts

def finishRun {Q : Type} (value : Nat → Q) : Nat → (Nat → Q) → Nat → Q
  | 0, old => old
  | n+1, old => Function.update (finishRun value n old) n (value n)

theorem finish_prefix {Q : Type} (value old : Nat → Q) (count j : Nat) :
    finishRun value count old j = if j<count then value j else old j := by
  induction count with
  | zero => simp [finishRun]
  | succ n ih =>
    by_cases h : j=n
    · subst j; simp [finishRun]
    · rw [finishRun,Function.update_of_ne h,ih]
      have hiff : (j<n+1) ↔ j<n := by omega
      simp only [hiff]

/-- The arbitrary-length finish contract tracks both overwritten prefix and
untouched suffix. The raw-vector length premise is what a Rust caller owes. -/
theorem finish_contract {Q : Type} (value old : Nat → Q) (length : Nat) :
    (∀ j, j<length → finishRun value length old j=value j) ∧
    (∀ j, length≤j → finishRun value length old j=old j) := by
  constructor
  · intro j hj; rw [finish_prefix,if_pos hj]
  · intro j hj; rw [finish_prefix,if_neg (by omega)]

/-- Index-based compact scan with the same early-rejection observation as
chunks_exact. Only complete 16-byte chunks contribute a predicate. -/
def scan (canonical : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, start => canonical start && scan canonical n (start+1)

theorem scan_accepts (canonical : Nat → Bool) (count start : Nat) :
    scan canonical count start = true ↔
      ∀ j, start≤j → j<start+count → canonical j=true := by
  induction count generalizing start with
  | zero => simp [scan]; omega
  | succ n ih =>
    rw [scan,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨hfirst,hrest⟩ j hlo hhi
      by_cases hj : j=start
      · simpa [hj] using hfirst
      · exact hrest j (by omega) (by omega)
    · intro h
      exact ⟨h start (by omega) (by omega),fun j hlo hhi => h j (by omega) (by omega)⟩

theorem compact_remainder_ignored (canonical : Nat → Bool) (chunks rest : Nat)
    (hr : rest<16) :
    scan canonical ((16*chunks+rest)/16) 0 = scan canonical chunks 0 := by
  congr 1
  omega

/-- No multiplication/addition overflow is needed to visit a complete chunk:
its end is at most the input length, itself a machine-sized slice length. -/
theorem scan_offset_bounds (length index : Nat) (hi : index<length/16) :
    16*index+16≤length ∧ index+1≤length/16 := by omega

#print axioms finish_prefix
#print axioms finish_contract
#print axioms scan_accepts
#print axioms compact_remainder_ignored
#print axioms scan_offset_bounds
end S8OwnedP6LoopContracts

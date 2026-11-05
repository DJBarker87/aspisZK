import NIZ_LAYOUT
set_option autoImplicit false
namespace NIZ_Unique

/-- Transcription of one checked key comparison; native source/body association
is recorded in NIZ_UNIQUE_STEP.json, not assumed by this definition. -/
def compare {Key : Type} [DecidableEq Key] (keys : Nat → Key) (i j : Nat) : Bool :=
  decide (keys i ≠ keys j)

def row {Key : Type} [DecidableEq Key] (keys : Nat → Key) (i j : Nat) : Nat → Bool
  | 0 => true
  | k+1 => compare keys i j && row keys i (j+1) k

def rows {Key : Type} [DecidableEq Key] (keys : Nat → Key) (n i : Nat) : Nat → Bool
  | 0 => true
  | k+1 => row keys i (i+1) (n-(i+1)) && rows keys n (i+1) k

/-- Arbitrary inner-loop induction: no finite transaction domain is imposed. -/
theorem row_sound {Key : Type} [DecidableEq Key] (keys : Nat → Key)
    (i j fuel : Nat) (ok : row keys i j fuel = true) :
    ∀ k, k < fuel → keys i ≠ keys (j+k) := by
  induction fuel generalizing j with
  | zero => intro k hk; omega
  | succ fuel ih =>
    have hs : _ ∧ _ := by simpa only [row, Bool.and_eq_true_iff] using ok
    intro k hk
    cases k with
    | zero => simpa [compare] using hs.1
    | succ k =>
      have h := ih (j+1) hs.2 k (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
#print axioms row_sound

/-- Every source lexicographic pair is covered by the outer-loop induction. -/
theorem rows_sound {Key : Type} [DecidableEq Key] (keys : Nat → Key)
    (n start fuel : Nat) (ok : rows keys n start fuel = true) :
    ∀ i j, start ≤ i → i < start+fuel → i < j → j < n → keys i ≠ keys j := by
  induction fuel generalizing start with
  | zero => intro i j hi hf; omega
  | succ fuel ih =>
    have hs : _ ∧ _ := by simpa only [rows, Bool.and_eq_true_iff] using ok
    intro i j hi hf hij hj
    by_cases eq : i = start
    · subst i
      have h := row_sound keys start (start+1) (n-(start+1)) hs.1
        (j-(start+1)) (by omega)
      have hj' : start+1+(j-(start+1)) = j := by omega
      rw [hj'] at h
      exact h
    · exact ih (start+1) hs.2 i j (by omega) (by omega) hij hj
#print axioms rows_sound

/-- Success of the transcribed all-pairs scan entails pairwise distinctness.
Binding its Boolean to the original helper's Result is a native/source packet,
not an additional premise silently discharged by this theorem. -/
theorem all_pairs_distinct {Key : Type} [DecidableEq Key] (keys : Nat → Key)
    (n : Nat) (ok : rows keys n 0 n = true) :
    ∀ i j, i < n → j < n → i ≠ j → keys i ≠ keys j := by
  intro i j hi hj ne
  by_cases lt : i < j
  · exact rows_sound keys n 0 n ok i j (by omega) (by omega) lt hj
  · exact Ne.symm (rows_sound keys n 0 n ok j i (by omega) (by omega) (by omega) hi)
#print axioms all_pairs_distinct

/-- Empty suffix and abort semantics cannot yield an unchecked successful suffix. -/
theorem equal_pair_rejects {Key : Type} [DecidableEq Key] (keys : Nat → Key)
    (i j fuel : Nat) (same : keys i = keys j) : row keys i j (fuel+1) = false := by
  simp [row, compare, same]
#print axioms equal_pair_rejects
end NIZ_Unique

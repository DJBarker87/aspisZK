import R1Z.ProverCommitAdaptiveHistory23
import R1Z.ProverCommitFuelOracle22
/-! Concrete coin-frame freshness for a bounded source nonzero window.
Earlier simulator coin requests retain their exact source coordinates;
observer queries are excluded by the existing seedGuess event. This does
not assert that all other internal caller requests belong to those classes. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFreshWindow24
open R0Z.FsStatement ProverCommitSimulatorOracle18 ProverCommitSeedEvent19
open QueryScanFreshProgram ProverCommitAdaptiveLaw23
attribute [local instance] Classical.propDecidable
variable {I A : Type} [DecidableEq I]

def linear (addr : Nat → I) (start : Nat) : (n : Nat) → Marked I A n
  | 0 => .done
  | n+1 => .scan (addr start) (fun _ => linear addr (start+1) n)

/-- Finite address shape proves the syntactic invariant on every answer
branch, rather than checking a sampled branch or assuming a random start. -/
theorem linear_fresh (addr : Nat → I) (start n : Nat) (seen : Finset I)
    (new : ∀ j < n, addr (start+j) ∉ seen)
    (distinct : ∀ i j, start ≤ i → i < start+n → start ≤ j → j < start+n →
      addr i = addr j → i = j) : Fresh (linear (A := A) addr start n) seen := by
  induction n generalizing start seen with
  | zero => exact True.intro
  | succ n ih =>
    constructor
    · simpa only [Nat.add_zero] using new 0 (Nat.zero_lt_succ n)
    · intro a
      apply ih (start+1) (insert (addr start) seen)
      · intro j hj
        rw [Finset.mem_insert,not_or]
        constructor
        · intro same
          have eq := distinct (start+1+j) start (by omega) (by omega)
            (by omega) (by omega) same
          omega
        · simpa only [Nat.add_assoc,Nat.add_comm 1 j] using new (j+1) (by omega)
      · intro i j hi₁ hi₂ hj₁ hj₂ same
        exact distinct i j (by omega) (by omega) (by omega) (by omega) same

def cursor (seed : OracleAnswer) (attempt : Fin 8) (stream : Fin 4) (counter : Nat) :
    List UInt8 := address (List.ofFn seed) attempt.val (UInt8.ofNat stream.val) counter

attribute [local irreducible] address indexedAddress cursor

theorem cursor_injective (seed : OracleAnswer) (attempt : Fin 8) (stream : Fin 4)
    (i j : Nat) (hi : i < 2^64) (hj : j < 2^64)
    (same : cursor seed attempt stream i = cursor seed attempt stream j) : i = j := by
  have eq := indexed_injective (count := 2^64) (Nat.le_refl _) seed
    (a₁ := (attempt,stream,⟨i,hi⟩)) (a₂ := (attempt,stream,⟨j,hj⟩)) (by
      simpa only [indexedAddress,cursor] using same)
  exact congrArg (fun z : Index (2^64) => z.2.2.val) eq

/-- The conservative seed event excludes even malformed suffixes, hence it
excludes every actual coin address at every counter as well. -/
theorem observer_fresh (queries : List Entry) (seed : OracleAnswer)
    (not_guessed : ¬ seedGuess queries seed) (attempt : Fin 8) (stream : Fin 4) (counter : Nat) :
    cursor seed attempt stream counter ∉ (queries.map Prod.fst).toFinset := by
  intro h
  obtain ⟨entry,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  apply not_guessed
  refine ⟨entry,member,?_⟩
  rw [same]
  unfold cursor
  exact source_point seed attempt.val (UInt8.ofNat stream.val) counter

/-- Source coordinate separation against all retained previous coin calls.
Different attempts and streams remain distinct after byte concatenation. -/
theorem earlier_coin_fresh (history : List (Index (2^64))) (seed : OracleAnswer)
    (attempt : Fin 8) (stream : Fin 4) (start counter : Nat)
    (lower : start ≤ counter) (room : counter < 2^64)
    (earlier : ∀ i ∈ history, i.1 ≠ attempt ∨ i.2.1 ≠ stream ∨ i.2.2.val < start) :
    cursor seed attempt stream counter ∉ (history.map (indexedAddress (count := 2^64) seed)).toFinset := by
  intro h
  obtain ⟨i,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  have eq := indexed_injective (count := 2^64) (Nat.le_refl _) seed
    (a₁ := i) (a₂ := (attempt,stream,⟨counter,room⟩)) (by
      simpa only [indexedAddress,cursor] using same)
  have old := earlier i member
  rcases old with different | different | before
  · exact different (congrArg Prod.fst eq)
  · exact different (congrArg (fun z : Index (2^64) => z.2.1) eq)
  · have count := congrArg (fun z : Index (2^64) => z.2.2.val) eq
    change i.2.2.val = counter at count
    omega

/-- Freshness of an actual five-counter source window, including a previous
adaptive coin prefix and the observer's complete ordered query suffix.
The remaining internal caller-address classification is not assumed here. -/
theorem source_window_fresh (history : List (Index (2^64))) (queries : List Entry)
    (seed : OracleAnswer) (attempt : Fin 8) (stream : Fin 4) (start : Nat)
    (room : start+5 ≤ 2^64)
    (earlier : ∀ i ∈ history, i.1 ≠ attempt ∨ i.2.1 ≠ stream ∨ i.2.2.val < start)
    (not_guessed : ¬ seedGuess queries seed) :
    Fresh (linear (A := OracleAnswer) (cursor seed attempt stream) start 5)
      ((history.map (indexedAddress (count := 2^64) seed)).toFinset ∪ (queries.map Prod.fst).toFinset) := by
  apply linear_fresh
  · intro j hj
    rw [Finset.mem_union,not_or]
    exact ⟨earlier_coin_fresh history seed attempt stream start (start+j) (by omega)
      (by omega) earlier,observer_fresh queries seed not_guessed attempt stream (start+j)⟩
  · intro i j hi₁ hi₂ hj₁ hj₂ same
    exact cursor_injective seed attempt stream i j (by omega) (by omega) same

#print axioms linear_fresh
#print axioms cursor_injective
#print axioms observer_fresh
#print axioms earlier_coin_fresh
#print axioms source_window_fresh
end R1Z.ProverCommitFreshWindow24

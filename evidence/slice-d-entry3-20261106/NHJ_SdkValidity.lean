import NHJ_SdkBracket
import Aeneas
set_option autoImplicit false
namespace NHJ_SdkValidity
open AspisR1.S2Trust

theorem tokens_fresh (guards : List Guard) (token : Nat)
    (fresh : guards.find? (fun g => g.token == token) = none) :
    ∀ g, g ∈ guards → g.token ≠ token := by
  induction guards with
  | nil => simp
  | cons first guards ih =>
    by_cases same : first.token = token
    · simp [List.find?_cons,same] at fresh
    · have rest : guards.find? (fun g => g.token == token) = none := by
        simpa [List.find?_cons,same] using fresh
      intro g member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact same
      · exact ih rest g member

theorem shared_count {F : Type} (s : Heap F) (cell token owner atCell : Nat) :
    count (acquire s cell token owner .shared) atCell .shared =
      if atCell = cell then count s atCell .shared + 1 else count s atCell .shared := by
  by_cases same : atCell = cell
  · subst atCell
    simp [count,acquire]
  · simp [count,acquire,same,Ne.symm same]

theorem exclusive_count {F : Type} (s : Heap F) (cell token owner atCell : Nat) :
    count (acquire s cell token owner .shared) atCell .exclusive = count s atCell .exclusive := by
  simp [count,acquire]

theorem counter {F : Type} (s : Heap F) (cell token owner atCell : Nat) :
    (acquire s cell token owner .shared).counter atCell =
      if atCell = cell then s.counter atCell + 1 else s.counter atCell := by
  by_cases same : atCell = cell <;> simp [acquire,put,same]

/-- Validity after a legal shared acquire, including existing external/shared
    guards. This supplies shared_deref/shared_drop's actual state invariant. -/
theorem acquired_valid {F : Type} (s : Heap F) (account token owner : Nat)
    (valid : Valid s) (enabled : Enabled s (.shared account token owner))
    (nonnegative : 0 ≤ s.counter (s.accounts account).1)
    (below : s.counter (s.accounts account).1 < maxCounter) :
    Valid (acquire s (s.accounts account).1 token owner .shared) := by
  rcases valid with ⟨pairs,bounds,live,owners⟩
  refine ⟨?_,?_,?_,owners⟩
  · apply List.Pairwise.cons
    · intro g member
      exact ⟨Ne.symm (tokens_fresh s.guards token enabled.2.1 g member),
        Ne.symm (enabled.2.2 g member)⟩
    · exact pairs
  · intro cell
    rw [counter,shared_count,exclusive_count]
    dsimp only [acquire]
    by_cases same : cell = (s.accounts account).1
    · subst cell
      simp only [if_true]
      obtain ⟨low,high,balance,exclusive,external⟩ := bounds (s.accounts account).1
      have excNonnegative : 0 ≤ count s (s.accounts account).1 .exclusive := by
        unfold count
        omega
      have excZero : count s (s.accounts account).1 .exclusive = 0 := by
        by_contra different
        have positive : 0 < count s (s.accounts account).1 .exclusive := by omega
        obtain ⟨extZero,sharedZero,excOne⟩ := exclusive positive
        rw [extZero,sharedZero,excOne] at balance
        omega
      have extNonnegative : ¬ s.external (s.accounts account).1 < 0 := by
        intro negative
        obtain ⟨sharedZero,excZero'⟩ := external negative
        rw [sharedZero,excZero'] at balance
        omega
      refine ⟨by omega,by omega,by omega,?_,?_⟩
      · intro impossible
        rw [excZero] at impossible
        omega
      · intro impossible
        exact False.elim (extNonnegative impossible)
    · simp only [if_neg same]
      exact bounds cell
  · intro g member
    change g ∈ _ :: s.guards at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨(owners account enabled.1).2,rfl⟩
    · exact live g member

theorem ambient_valid {F : Type} (s : Heap F) (valid : Valid s) (ambient : F) :
    Valid {s with ambient := ambient} := valid
#print axioms tokens_fresh
#print axioms shared_count
#print axioms exclusive_count
#print axioms counter
#print axioms acquired_valid
#print axioms ambient_valid
end NHJ_SdkValidity

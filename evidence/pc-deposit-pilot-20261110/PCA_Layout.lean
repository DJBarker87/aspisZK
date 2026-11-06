import NIZ_LAYOUT
import PCA_RowSpec_POOL_332
set_option autoImplicit false
namespace PCA

theorem count_ok (expected : Nat) (s : PCA_State) :
    (countReference expected s).reply = .ok () ↔ s.accountCount = expected := by
  by_cases h : s.accountCount = expected
  · simp [countReference,h]
  · simp only [countReference,h,if_false]
    split <;> simp

theorem count_frame (expected : Nat) (s : PCA_State) :
    (countReference expected s).state = s ∧ (countReference expected s).events = [] := ⟨rfl,rfl⟩

/-- Exact info order from frozen vault.rs, reused index proof from NIZ. -/
def transferPassed (m : NIZ_LAYOUT.DepositMode) : List Nat :=
  let n := NIZ_LAYOUT.depositStart m
  [n+1,n,n+3,n+2,n+4]

theorem held_excluded (m : NIZ_LAYOUT.DepositMode) (g t : Nat)
    (held : NIZ_LAYOUT.DepositGuard m g) (passed : t ∈ transferPassed m) : g ≠ t := by
  simp only [transferPassed, List.mem_cons, List.not_mem_nil, or_false] at passed
  rcases passed with h | h | h | h | h
  · subst t; exact NIZ_LAYOUT.deposit_separate m g 1 held
  · subst t; simpa using NIZ_LAYOUT.deposit_separate m g 0 held
  · subst t; exact NIZ_LAYOUT.deposit_separate m g 3 held
  · subst t; exact NIZ_LAYOUT.deposit_separate m g 2 held
  · subst t; exact NIZ_LAYOUT.deposit_separate m g 4 held

#print axioms count_ok
#print axioms count_frame
#print axioms held_excluded
end PCA

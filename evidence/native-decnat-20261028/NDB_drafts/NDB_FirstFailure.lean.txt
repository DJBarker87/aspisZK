import Mathlib.Data.Nat.Find
set_option autoImplicit false
namespace NDB_FirstFailure
/-- Symbolic first failure, without enumerating the finite buffer. -/
theorem first (n : Nat) (good : Nat → Prop) (failure : ¬∀ j, j<n → good j) :
    ∃ bad, bad<n ∧ ¬good bad ∧ ∀ j, j<bad → good j := by
  classical
  have witness : ∃ j, j<n ∧ ¬good j := by
    by_contra h
    apply failure
    intro j hj
    by_contra bad
    exact h ⟨j,hj,bad⟩
  refine ⟨Nat.find witness,(Nat.find_spec witness).1,(Nat.find_spec witness).2,?_⟩
  intro j hj
  by_contra bad
  have minimal:=Nat.find_min' witness (show j<n ∧ ¬good j from ⟨by omega,bad⟩)
  omega
/-- Projection indices used by the repaired master/checkpoint Box harnesses. -/
theorem master_sequences (j : Nat) (bound : j<8) :
    230+j<238 ∧ 230+j-230=j := by omega

theorem checkpoint_sequences (j : Nat) (bound : j<8) :
    74+j<82 ∧ 74+j-74=j := by omega

theorem master_byte_block (block j : Nat) (blocks : block<7) (bound : j<32) :
    6+32*block+j<238 ∧
      6+32*block ≤ 6+32*block+j ∧
      6+32*block+j < 6+32*(block+1) := by omega
#print axioms first
#print axioms master_sequences
#print axioms checkpoint_sequences
#print axioms master_byte_block
end NDB_FirstFailure

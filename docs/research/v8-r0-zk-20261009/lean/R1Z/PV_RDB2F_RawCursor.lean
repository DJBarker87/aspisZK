import R1Z.PV_RDB2E_PointerOffsets
namespace R1Z.PV_RDB2F_RawCursor
set_option autoImplicit false
abbrev address := PV_RDB2E_PointerOffsets.address
/-- Non-ZST branch of IterMut::next_back: empty check, pre-decrement, return. -/
def back (front past : Nat) : Option (Nat × Nat) :=
  if front=past then none else some (past-1,past-1)
/-- Non-ZST branch of IterMut::next: empty check, save old pointer, post-increment. -/
def forward (front past : Nat) : Option (Nat × Nat) :=
  if front=past then none else some (front,front+1)

theorem back_bounds (front past : Nat) (h : front<past) :
    back front past=some (past-1,past-1) ∧ front≤past-1 ∧ past-1<past := by
  simp only [back,show front≠past by omega,if_false]
  omega

theorem forward_bounds (front past : Nat) (h : front<past) :
    forward front past=some (front,front+1) ∧ front+1≤past := by
  simp only [forward,show front≠past by omega,if_false]
  omega

theorem exact_empty (front past : Nat) (h : front≤past) (base : Nat) :
    address base front=address base past ↔ ¬front<past := by
  rw [PV_RDB2E_PointerOffsets.injective]
  omega

theorem backward_pointer (base front past : Nat) (h : front<past) :
    address base past-4=address base (past-1) :=
  PV_RDB2E_PointerOffsets.previous base past (by omega)

theorem forward_pointer (base front : Nat) :
    address base front+4=address base (front+1) := PV_RDB2E_PointerOffsets.next base front

theorem mixed_no_repeat (front past : Nat) (h : front+1<past) :
    front≠past-1 ∧ front+1≤past-1 := by omega

#print axioms back_bounds
#print axioms forward_bounds
#print axioms exact_empty
#print axioms backward_pointer
#print axioms forward_pointer
#print axioms mixed_no_repeat
end R1Z.PV_RDB2F_RawCursor

import Port4B_SlotInstall

set_option autoImplicit false
namespace AspisR1.NBE_SlotLoop
open OraclePortSelectedDraft

/-- Forward denotation of the native slot_offset loop. Each step is the
source at+=32*SLOT_NODES[i]; i+=1, without a whole-loop native gate. -/
def offset : Nat → Nat
  | 0 => 28359
  | n+1 => offset n + 32*capacity n

/-- The same offset as the installed cohort, including the terminal boundary. -/
theorem offset_eq (n : Nat) : offset n = slotStart n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [offset, ih, Port4B_SlotInstall.offset_step]

/-- Each native iteration's accumulator satisfies the gate bound. -/
theorem reached_bound (n : Nat) (bound : n ≤ 6) : offset n ≤ 57607 := by
  rw [offset_eq]
  exact Port4B_SlotInstall.offset_bound n bound

#print axioms offset_eq
#print axioms reached_bound
end AspisR1.NBE_SlotLoop

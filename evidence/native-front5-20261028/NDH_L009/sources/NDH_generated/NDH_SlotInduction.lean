import NDH_Slots
set_option autoImplicit false
namespace NDH_SlotInduction
open AspisR1.OraclePortSelectedDraft

/-- Integer-valued trace supplied by the source's checked scalar step. -/
inductive Trace : Nat → Nat → Prop where
 | initial : Trace 0 28359
 | step {i at next : Nat} (prior : Trace i at) (domain : i < 6)
     (update : next = at + 32 * capacity i) : Trace (i+1) next

theorem invariant {i at : Nat} (trace : Trace i at) :
    i ≤ 6 ∧ at = slotStart i := by
  induction trace with
  | initial => exact ⟨by omega, rfl⟩
  | @step i at next prior domain update ih =>
    constructor
    · omega
    · rw [update, ih.2, ← NDH_Slots.step]

theorem exists_trace (i : Nat) (domain : i ≤ 6) : Trace i (slotStart i) := by
  induction i with
  | zero => exact Trace.initial
  | succ i ih =>
    exact Trace.step (ih (by omega)) (by omega) (NDH_Slots.step i)

theorem completion {slot at : Nat} (trace : Trace slot at) :
    at = slotStart slot ∧ at ≤ 57607 := by
  obtain ⟨domain, value⟩ := invariant trace
  exact ⟨value, value ▸ AspisR1.Port4B_SlotInstall.offset_bound slot domain⟩

#print axioms invariant
#print axioms exists_trace
#print axioms completion
end NDH_SlotInduction

import NDH_Slots
set_option autoImplicit false
namespace NDH_SlotInduction
open AspisR1.OraclePortSelectedDraft

/-- Integer-valued trace supplied by the source's checked scalar step. -/
inductive Trace : Nat → Nat → Prop where
 | initial : Trace 0 28359
 | step {i addr next : Nat} (prior : Trace i addr) (domain : i < 6)
     (update : next = addr + 32 * capacity i) : Trace (i+1) next

theorem invariant {i addr : Nat} (trace : Trace i addr) :
    i ≤ 6 ∧ addr = slotStart i := by
  induction trace with
  | initial => exact ⟨by omega, rfl⟩
  | @step i addr next prior domain update ih =>
    constructor
    · omega
    · rw [update, ih.2, ← NDH_Slots.step]

theorem exists_trace (i : Nat) (domain : i ≤ 6) : Trace i (slotStart i) := by
  induction i with
  | zero => exact Trace.initial
  | succ i ih =>
    exact Trace.step (ih (by omega)) (by omega) (NDH_Slots.step i)

theorem completion {slot addr : Nat} (trace : Trace slot addr) :
    addr = slotStart slot ∧ addr ≤ 57607 := by
  obtain ⟨domain, value⟩ := invariant trace
  refine ⟨value, ?_⟩
  rw [value]
  exact AspisR1.Port4B_SlotInstall.offset_bound slot domain

#print axioms invariant
#print axioms exists_trace
#print axioms completion
end NDH_SlotInduction

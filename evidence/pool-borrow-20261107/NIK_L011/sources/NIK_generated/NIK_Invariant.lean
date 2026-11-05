import NIK_Footprint
set_option autoImplicit false
namespace NIK_Invariant
open AspisR1.S2Trust

/-- A conditional library scope calculus. No production child/CPI frame is
asserted here; its constructor exposes the exact missing physical-frame law. -/
inductive ScopeStep {F : Type} : Heap F → Heap F → Prop where
  | shared (s : Heap F) (c t o : Nat) :
      ScopeStep s (release (acquire s c t o .shared)
        ⟨t,c,o,.shared,(s.payload c).descriptor⟩)
  | exclusive (s : Heap F) (c t o : Nat) (free : s.counter c = 0) :
      ScopeStep s (release (acquire s c t o .exclusive)
        ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩)
  | framedChild (s u : Heap F) (cells : u.accounts = s.accounts)
      (counters : u.counter = s.counter) : ScopeStep s u

theorem step_room {F : Type} {s u : Heap F} (step : ScopeStep s u)
    (a : Nat) (room : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a := by
  cases step with
  | shared c t o => exact NIE_BorrowRelease.shared_room_roundtrip _ c t o a room
  | exclusive c t o free => exact NIK_Counter.exclusive_scope_room _ c t o a free room
  | framedChild _ cells counters => exact NIK_Counter.room_of_frame _ _ cells counters a room
#print axioms step_room

inductive ScopeRun {F : Type} : Heap F → Heap F → Prop where
  | initial (s : Heap F) : ScopeRun s s
  | next {s u v : Heap F} (prior : ScopeRun s u) (step : ScopeStep u v) : ScopeRun s v

/-- Model induction only. Instantiating ScopeRun with the deployed Pool prefix,
including callbacks, aliases and CPI, remains a native correctness obligation. -/
theorem scope_model_invariant {F : Type} {s u : Heap F}
    (run : ScopeRun s u) (a : Nat) (room : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a := by
  induction run with
  | initial => exact room
  | next prior step ih => exact step_room step a ih
#print axioms scope_model_invariant
end NIK_Invariant

import NMM_OrderedPrefix
set_option autoImplicit false
set_option pp.proofs false
namespace NMM_TraceState

structure State (E : Type) where
 count : Nat
 events : List (Nat × E)

def initial (E : Type) : State E := ⟨0,[]⟩
def Valid {E : Type} (s : State E) : Prop := s.events.map Prod.fst = List.range s.count

def push {E : Type} (s : State E) (ordinal : Nat) (event : E) : State E :=
 ⟨s.count+1,s.events++[(ordinal,event)]⟩

/-- A stopped arm contains only an ordered event prefix, with no heap or
post-abort payload. E can include arguments and an optional callee reply. -/
inductive Outcome (A E : Type) where
 | returned : A → State E → Outcome A E
 | stopped : List (Nat × E) → Outcome A E

def stop {A E : Type} (s : State E) : Outcome A E := .stopped s.events

theorem initial_valid (E : Type) : Valid (initial E) := rfl

theorem push_valid {E : Type} (s : State E) (ordinal : Nat) (event : E)
 (before : Valid s) (checked : ordinal=s.count) : Valid (push s ordinal event) := by
 unfold Valid push
 simp only [List.map_append,List.map_cons,List.map_nil]
 rw [before,checked,NMM_OrderedPrefix.next]

theorem stopped_prefix {A E : Type} (s : State E) (valid : Valid s) (bound : s.count≤21) :
 ∃ events, stop (A:=A) s = .stopped events ∧
 ∃ n, n≤21 ∧ events.map Prod.fst=List.range n :=
 ⟨s.events,rfl,s.count,bound,valid⟩

#print initial_valid
#print axioms initial_valid
#print push_valid
#print axioms push_valid
#print stopped_prefix
#print axioms stopped_prefix
end NMM_TraceState

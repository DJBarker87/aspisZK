import S2E_Types

/-! Runtime syscall laws. `RuntimePremise` is the primitive set_return_data
semantics, not an emit/ASQ8 success assumption. Abort/rollback is outside a
reached, returning syscall step. Earlier events are never removed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2I.ReturnData

inductive Event (Other : Type) where
  | setReturnData : List U8 → Event Other
  | other : Other → Event Other

structure State (Accounts Other : Type) where
  accounts : Accounts
  returnData : List U8
  events : List (Event Other)

def set {A E : Type} (s : State A E) (bytes : List U8) : State A E :=
  {s with returnData := bytes, events := s.events ++ [.setReturnData bytes]}

/-- Pinned runtime interpretation required at a reached syscall. Account
state includes all account/lamport metadata. Other native state must be
carried by the chosen carrier or port; no universal native port is inferred. -/
def RuntimePremise {A E : Type}
    (syscall : State A E → List U8 → Result (State A E)) : Prop :=
  ∀ s bytes, syscall s bytes = ok (set s bytes)

def clear {A E : Type} (syscall : State A E → List U8 → Result (State A E))
    (s : State A E) := syscall s []

theorem clear_contract {A E : Type}
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (s : State A E) :
    clear syscall s = ok (set s []) ∧
    (set s []).accounts = s.accounts ∧
    (set s []).returnData = [] ∧
    (set s []).events = s.events ++ [.setReturnData []] :=
  ⟨runtime s [],rfl,rfl,rfl⟩

/-- ASQ8 is called on the post-clear state, including on inner rejection.
This theorem makes no claim that ASQ8 itself preserves accounts or events. -/
theorem before_asq8 {A E B : Type}
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (s : State A E)
    (validate_asq8 : State A E → Result B) :
    (do let cleared ← clear syscall s; validate_asq8 cleared) =
      validate_asq8 (set s []) := by
  rw [(clear_contract syscall runtime s).1]
  rfl

theorem rejected_asq8 {A E B : Type}
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (s : State A E)
    (validate_asq8 : State A E → Result B) (reply : B)
    (rejected : validate_asq8 (set s []) = ok reply) :
    (do let cleared ← clear syscall s; validate_asq8 cleared) = ok reply := by
  rw [before_asq8 syscall runtime s validate_asq8,rejected]

theorem nonempty_event {A E : Type}
    (syscall : State A E → List U8 → Result (State A E))
    (runtime : RuntimePremise syscall) (s : State A E) (bytes : List U8)
    (width : bytes.length = 792) :
    syscall s bytes = ok (set s bytes) ∧ bytes ≠ [] ∧
    (set s bytes).accounts = s.accounts ∧
    (set s bytes).events = s.events ++ [.setReturnData bytes] := by
  refine ⟨runtime s bytes,?_,rfl,rfl⟩
  intro h
  rw [h] at width
  contradiction

#print axioms clear_contract
#print axioms before_asq8
#print axioms rejected_asq8
#print axioms nonempty_event
end AspisR1.S2I.ReturnData

import PCD_State
set_option autoImplicit false
namespace PCD

theorem bind_error {α β : Type} (e : ProgramError) (s : State) (earlier : List Event)
    (next : α → State → Execution β) :
    bind (⟨.error e,s,earlier⟩ : Execution α) next = ⟨.error e,s,earlier⟩ := rfl

theorem bind_abort {α β : Type} (s : State) (earlier : List Event)
    (next : α → State → Execution β) :
    bind (⟨.abort,s,earlier⟩ : Execution α) next = ⟨.abort,s,earlier⟩ := rfl

theorem bind_diverge {α β : Type} (s : State) (earlier : List Event)
    (next : α → State → Execution β) :
    bind (⟨.diverge,s,earlier⟩ : Execution α) next = ⟨.diverge,s,earlier⟩ := rfl

theorem bind_ok {α β : Type} (a : α) (s : State) (earlier : List Event)
    (next : α → State → Execution β) :
    bind (⟨.ok a,s,earlier⟩ : Execution α) next =
      ⟨(next a s).reply,(next a s).state,earlier ++ (next a s).events⟩ := rfl

/-- One state is threaded through all occurrences, with no fresh entry admission. -/
theorem bind_assoc {α β γ : Type} (first : Execution α)
    (f : α → State → Execution β) (g : β → State → Execution γ) :
    bind (bind first f) g = bind first (fun a s => bind (f a s) g) := by
  rcases first with ⟨reply,s,events⟩
  cases reply with
  | ok a =>
    unfold bind
    cases h : (f a s).reply <;> simp [bind, h, List.append_assoc]
  | error e => rfl
  | abort => rfl
  | diverge => rfl
#print axioms bind_error
#print axioms bind_abort
#print axioms bind_diverge
#print axioms bind_ok
#print axioms bind_assoc
end PCD

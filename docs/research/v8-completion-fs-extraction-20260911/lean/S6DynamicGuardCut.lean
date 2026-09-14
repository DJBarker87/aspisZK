import S6GuardErasure

/-! FIRST-ATTEMPT draft. A pure terminal check can be removed while retaining
all semantic computation, including its dynamic context and complete oracle.
No claim that the selected Rust terminal is effect-free follows from this file.
-/
set_option autoImplicit false
namespace AspisS6
universe u v w x y
variable {I : Type u} {O : Type v} {C : Type w} {A : Type x} {S : Type y}

def guardedThen (answer : I → S → O × S)
    (prelude : Program I O C) (guard : C → Bool)
    (suffix : C → Program I O A) (s : S) : Option A × S :=
  let earlier := run answer prelude s
  match earlier.1 with
  | none => (none, earlier.2)
  | some context =>
      if guard context then run answer (suffix context) earlier.2
      else (none, earlier.2)

def relaxedThen (answer : I → S → O × S)
    (prelude : Program I O C) (suffix : C → Program I O A)
    (s : S) : Option A × S :=
  let earlier := run answer prelude s
  match earlier.1 with
  | none => (none, earlier.2)
  | some context => run answer (suffix context) earlier.2

/-- Construct the very context and prelude state used by the accepted run.
They are outputs of execution, not values supplied from a completed replay. -/
theorem accepted_guarded_context
    (answer : I → S → O × S) (prelude : Program I O C)
    (guard : C → Bool) (suffix : C → Program I O A)
    (s : S) (a : A) (final : S)
    (success : guardedThen answer prelude guard suffix s = (some a, final)) :
    ∃ context prior,
      run answer prelude s = (some context, prior) ∧
      guard context = true ∧
      run answer (suffix context) prior = (some a, final) := by
  cases hp : run answer prelude s with
  | mk result prior =>
      cases result with
      | none => simp [guardedThen, hp] at success
      | some context =>
          cases hg : guard context with
          | false => simp [guardedThen, hp, hg] at success
          | true =>
              refine ⟨context, prior, rfl, hg, ?_⟩
              simpa [guardedThen, hp, hg] using success

theorem accepted_guarded_is_relaxed
    (answer : I → S → O × S) (prelude : Program I O C)
    (guard : C → Bool) (suffix : C → Program I O A)
    (s : S) (a : A) (final : S)
    (success : guardedThen answer prelude guard suffix s = (some a, final)) :
    relaxedThen answer prelude suffix s = (some a, final) := by
  obtain ⟨context, prior, hp, _, hs⟩ :=
    accepted_guarded_context answer prelude guard suffix s a final success
  simpa [relaxedThen, hp] using hs

#print axioms accepted_guarded_context
#print axioms accepted_guarded_is_relaxed
end AspisS6

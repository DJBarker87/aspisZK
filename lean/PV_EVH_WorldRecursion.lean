import PV_EVH_WorldLoop
set_option autoImplicit false
namespace PV_EVH_WorldRecursion
open Aeneas Aeneas.Std PV_EVH_World PV_EVH_WorldLoop
variable {S A : Type}

/-- Erasure into a source recursive equation. Exhaustion has no Result claim.
No whole source recurrence is normalized. -/
theorem fixed_finished_recursive (body : S → M (ControlFlow S A))
    (source : S → Result (ControlFlow S A)) (recur : S → Result A)
    (equation : ∀ s, recur s = Aeneas.Std.bind (source s) (fun cf =>
      match cf with | .done a => .ok a | .cont next => recur next))
    (compatible : ∀ s, FixedView (body s) (source s))
    (n : Nat) (s : S) (w : World) (r : Result A)
    (finished : (PV_EVH_WorldLoop.loop body n s w).status = .finished r) : recur s = r := by
  induction n generalizing s w r with
  | zero => cases finished
  | succ n ih =>
    cases hs : source s with
    | fail e =>
      have he := compatible s w
      rw [hs] at he
      simp only [PV_EVH_WorldLoop.loop,he] at finished
      cases finished
      rw [equation,hs]
      rfl
    | div =>
      have he := compatible s w
      rw [hs] at he
      simp only [PV_EVH_WorldLoop.loop,he] at finished
      cases finished
      rw [equation,hs]
      rfl
    | ok cf =>
      cases cf with
      | done a =>
        have he := compatible s w
        rw [hs] at he
        simp only [PV_EVH_WorldLoop.loop,he] at finished
        cases finished
        rw [equation,hs]
        rfl
      | cont next =>
        have he := compatible s w
        rw [hs] at he
        simp only [PV_EVH_WorldLoop.loop,he] at finished
        rw [equation,hs]
        exact ih next (body s w).world r finished

#print axioms fixed_finished_recursive
end PV_EVH_WorldRecursion

import Std

/-! FIRST-ATTEMPT draft. Check compilation before promotion.
This is a deterministic control theorem. It does not identify arbitrary Rust
callbacks with pure functions, or establish a random-oracle probability law.
-/
set_option autoImplicit false
namespace AspisS6
universe u v w x
inductive Program (I : Type u) (O : Type v) (A : Type w) where
  | done (value : A)
  | abort
  | ask (input : I) (next : O → Program I O A)
  | check (condition : Bool) (next : Program I O A)

variable {I : Type u} {O : Type v} {A : Type w} {S : Type x}

def run (answer : I → S → O × S) : Program I O A → S → Option A × S
  | .done a, s => (some a, s)
  | .abort, s => (none, s)
  | .ask i k, s => let r := answer i s; run answer (k r.1) r.2
  | .check b k, s => if b then run answer k s else (none, s)

def eraseChecks : Program I O A → Program I O A
  | .done a => .done a
  | .abort => .abort
  | .ask i k => .ask i (fun a => eraseChecks (k a))
  | .check _ k => eraseChecks k

/-- Includes the COMPLETE S; instantiate S with cache, mixed history and
fresh counter together. The statement does not project to fresh records. -/
theorem accepting_run_survives_erasure
    (answer : I → S → O × S) (program : Program I O A) :
    ∀ s a final, run answer program s = (some a, final) →
      run answer (eraseChecks program) s = (some a, final) := by
  induction program with
  | done value =>
      intro s a final success
      simpa only [eraseChecks] using success
  | abort =>
      intro s a final success
      simp [run] at success
  | ask input next ih =>
      intro s a final success
      change run answer (next (answer input s).1) (answer input s).2 =
        (some a, final) at success
      change run answer (eraseChecks (next (answer input s).1))
        (answer input s).2 = (some a, final)
      exact ih (answer input s).1 (answer input s).2 a final success
  | check condition next ih =>
      intro s a final success
      cases condition with
      | false => simp [run] at success
      | true =>
          exact ih s a final (by simpa [run] using success)

#print axioms accepting_run_survives_erasure
end AspisS6


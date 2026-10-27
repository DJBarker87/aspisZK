import R1Z.ProverCommitReferenceSource

/-! Composition without unrolling the sampler. The relational step premise is
explicit: a Kani receipt is not an axiom or an imported Lean source theorem. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSamplerComposition

/-- A stopped sampler carries its value and no longer consumes words. -/
def carry {S A : Type} (step : S → Option A × S) : Option A × S → Option A × S
  | (some a, s) => (some a, s)
  | (none, s) => step s

/-- Exactly n carried transitions, including absorbing successful states. -/
def run {S A : Type} (step : S → Option A × S) : Nat → Option A × S → Option A × S
  | 0, x => x
  | n+1, x => run step n (carry step x)

/-- The actual early-return loop shape, with n remaining tries. -/
def early {S A : Type} (step : S → Option A × S) : Nat → S → Option A × S
  | 0, s => (none, s)
  | n+1, s => match step s with
    | (some a, t) => (some a, t)
    | (none, t) => early step n t

theorem run_success {S A : Type} (step : S → Option A × S)
    (n : Nat) (a : A) (s : S) : run step n (some a, s) = (some a, s) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem early_eq_run {S A : Type} (step : S → Option A × S)
    (n : Nat) (s : S) : early step n s = run step n (none, s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [early, run, carry]
    cases h : step s with
    | mk value t =>
      cases value with
      | none => exact ih t
      | some a => exact (run_success step n a t).symm

/-- Invariant-restricted relational composition. Both transitions preserve the
valid-state invariant, so one local equality suffices for every loop length. -/
theorem run_refines {S A : Type} (left right : S → Option A × S)
    (valid : S → Prop)
    (same : ∀ s, valid s → left s = right s)
    (closed : ∀ s, valid s → valid (left s).2)
    (n : Nat) (x : Option A × S) (hx : valid x.2) :
    run left n x = run right n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨value, s⟩
    cases value with
    | some a => rw [run_success, run_success]
    | none =>
      simp only [run, carry]
      rw [← same s hx]
      exact ih (left s) (closed s hx)

theorem sixteen_tries {S A : Type} (left right : S → Option A × S)
    (valid : S → Prop)
    (same : ∀ s, valid s → left s = right s)
    (closed : ∀ s, valid s → valid (left s).2)
    (s : S) (hs : valid s) :
    early left 16 s = run right 16 (none, s) := by
  rw [early_eq_run]
  exact run_refines left right valid same closed 16 (none, s) hs

#print axioms run_success
#print axioms early_eq_run
#print axioms run_refines
#print axioms sixteen_tries
end R1Z.ProverCommitSamplerComposition

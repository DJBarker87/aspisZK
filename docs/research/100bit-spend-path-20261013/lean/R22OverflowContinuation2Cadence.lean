import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Numerical induction for the phase contract checked against the frozen row
body by Kani. This is not a Rust/Aeneas correspondence or an endpoint theorem.
The caller still has to visit each mutable row exactly once before incrementing
terms. The namespace is distinct from the sibling endpoint worker. -/
set_option autoImplicit false
namespace AspisR1.R22OverflowContinuation2Cadence

def bound (t value : Nat) : Prop :=
  value < 17179869184 + (t % 4) * 4611686009837453316

def step (t value product : Nat) : Nat :=
  let total := value + product
  if t % 4 = 3 then total % 2147483648 + total / 2147483648 else total

theorem step_safe (t value product : Nat) (hv : bound t value)
    (hp : product ≤ 4611686009837453316) :
    value + product < 18446744073709551616 ∧
    bound (t + 1) (step t value product) := by
  unfold bound at *
  dsimp only [step]
  split <;> omega

def run (t value : Nat) : List Nat → Nat
  | [] => value
  | product :: rest => run (t + 1) (step t value product) rest

theorem run_bound (products : List Nat) (t value : Nat)
    (hv : bound t value)
    (hp : ∀ p ∈ products, p ≤ 4611686009837453316) :
    bound (t + products.length) (run t value products) := by
  induction products generalizing t value with
  | nil => simpa only [run, List.length_nil, Nat.add_zero] using hv
  | cons p ps ih =>
    have hs := (step_safe t value p hv (hp p (by simp))).2
    have hps : ∀ x ∈ ps, x ≤ 4611686009837453316 := by
      intro x hx
      exact hp x (by simp [hx])
    have hi := ih (t + 1) (step t value p) hs hps
    simpa only [run, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hi

/-- Pointwise lifting preserves the same phase for every row. The source loop's
one-visit property is a separate obligation, rather than an implicit assumption
that a shared term counter advances at each individual row update. -/
theorem all_rows_step {Row : Type} (t : Nat) (rows products : Row → Nat)
    (hv : ∀ row, bound t (rows row))
    (hp : ∀ row, products row ≤ 4611686009837453316) :
    ∀ row, bound (t + 1) (step t (rows row) (products row)) := by
  intro row
  exact (step_safe t (rows row) (products row) (hv row) (hp row)).2

/-- Frozen resume has cursor 712 before weights, and a 32-byte checksum after
weights. Both admitted weight widths fit the proved 4,880-byte reader domain. -/
theorem checkpoint_schedule (width i : Nat) (hw : width = 64 ∨ width = 256)
    (hi : i < width) :
    712 + 16 * i + 16 ≤ 712 + 16 * width ∧
    712 + 16 * width + 32 = 744 + 16 * width ∧
    744 + 16 * width ≤ 4880 ∧ 712 + 16 * i + 16 < 57607 := by
  rcases hw with h | h <;> omega

#print axioms step_safe
#print axioms run_bound
#print axioms all_rows_step
#print axioms checkpoint_schedule
end AspisR1.R22OverflowContinuation2Cadence

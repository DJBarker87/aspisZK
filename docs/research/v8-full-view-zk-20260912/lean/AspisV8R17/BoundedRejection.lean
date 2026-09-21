import AspisV8Privacy.FiniteGames
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact finite-tape rejection counting. Uniform independent tapes are an
ideal sampler model, not an assumed law for cached shared-oracle answers. -/
set_option autoImplicit false
namespace AspisV8R17.BoundedRejection
open AspisV8Privacy
variable {D : Type*}

def firstAccepted (accept : D → Bool) : List D → Option D
  | [] => none
  | x::xs => if accept x then some x else firstAccepted accept xs

def sample (accept : D → Bool) {n : ℕ} (tape : Fin n → D) : Option D :=
  firstAccepted accept (List.ofFn tape)

theorem firstAccepted_map (accept : D → Bool) (e : D ≃ D)
    (preserves : ∀ x, accept (e x) = accept x) (xs : List D) :
    firstAccepted accept (xs.map e) = (firstAccepted accept xs).map e := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, firstAccepted, preserves]
      split <;> simp_all

theorem sample_map (accept : D → Bool) (e : D ≃ D)
    (preserves : ∀ x, accept (e x) = accept x) {n : ℕ} (tape : Fin n → D) :
    sample accept (fun i => e (tape i)) = (sample accept tape).map e := by
  simpa only [sample, List.map_ofFn, Function.comp_def] using
    firstAccepted_map accept e preserves (List.ofFn tape)

theorem firstAccepted_none (accept : D → Bool) (xs : List D) :
    firstAccepted accept xs = none ↔ ∀ x ∈ xs, accept x = false := by
  induction xs with
  | nil => simp [firstAccepted]
  | cons x xs ih =>
      cases hx : accept x <;> simp [firstAccepted,hx,ih]

theorem sample_none (accept : D → Bool) {n : ℕ} (tape : Fin n → D) :
    sample accept tape = none ↔ ∀ i, accept (tape i) = false := by
  simp [sample, firstAccepted_none, List.mem_ofFn]

def failureFiberEquiv (accept : D → Bool) (n : ℕ) :
    {tape : Fin n → D // sample accept tape = none} ≃
      (Fin n → {x : D // accept x = false}) where
  toFun tape i := ⟨tape.val i, (sample_none accept tape.val).mp tape.property i⟩
  invFun tape := ⟨fun i => (tape i).val, (sample_none accept _).mpr (fun i => (tape i).property)⟩
  left_inv tape := by rfl
  right_inv tape := by rfl

theorem failure_count [Fintype D] (accept : D → Bool) (n : ℕ) :
    fiberCount (@sample D accept n) none =
      (Fintype.card {x : D // accept x = false})^n := by
  classical
  unfold fiberCount
  simp only [Fintype.card_eq_nat_card]
  rw [Nat.card_congr (failureFiberEquiv accept n), Nat.card_fun]
  simp

def outputFiberEquiv (accept : D → Bool) (e : D ≃ D)
    (preserves : ∀ x, accept (e x) = accept x) (n : ℕ) (y : Option D) :
    {tape : Fin n → D // sample accept tape = y} ≃
      {tape : Fin n → D // sample accept tape = y.map e} where
  toFun tape := ⟨fun i => e (tape.val i), by rw [sample_map accept e preserves, tape.property]⟩
  invFun tape := ⟨fun i => e.symm (tape.val i), by
    have hp : ∀ x, accept (e.symm x) = accept x := by
      intro x
      simpa using (preserves (e.symm x)).symm
    rw [sample_map accept e.symm hp, tape.property]
    cases y <;> simp⟩
  left_inv tape := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv tape := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

theorem accepted_counts_equal [Fintype D] [DecidableEq D]
    (accept : D → Bool) (n : ℕ) (a b : D) (ha : accept a = true) (hb : accept b = true) :
    fiberCount (@sample D accept n) (some a) = fiberCount (@sample D accept n) (some b) := by
  classical
  have hp : ∀ x, accept (Equiv.swap a b x) = accept x := by
    intro x
    by_cases hxa : x=a
    · subst x; simp [ha,hb]
    by_cases hxb : x=b
    · subst x; simp [ha,hb]
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
  unfold fiberCount
  simp only [Fintype.card_eq_nat_card]
  simpa using Nat.card_congr (outputFiberEquiv accept (Equiv.swap a b) hp n (some a))

theorem failure_probability [Fintype D] [Nonempty D] (accept : D → Bool) (n : ℕ) :
    uniformProbability (@sample D accept n) none =
      ((Fintype.card {x : D // accept x = false} : ℚ)^n) /
        ((Fintype.card D : ℚ)^n) := by
  unfold uniformProbability
  rw [failure_count]
  simp

theorem accepted_probabilities_equal [Fintype D] [Nonempty D] [DecidableEq D]
    (accept : D → Bool) (n : ℕ) (a b : D) (ha : accept a = true) (hb : accept b = true) :
    uniformProbability (@sample D accept n) (some a) =
      uniformProbability (@sample D accept n) (some b) := by
  unfold uniformProbability
  rw [accepted_counts_equal accept n a b ha hb]

#print axioms failure_probability
#print axioms accepted_probabilities_equal
#print axioms firstAccepted_map
#print axioms sample_map
#print axioms firstAccepted_none
#print axioms sample_none
#print axioms failure_count
#print axioms accepted_counts_equal
end AspisV8R17.BoundedRejection

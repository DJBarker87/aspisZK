import R1ResidualBatch

/-! A symbolic accumulator recurrence with the same arithmetic shape used
for a challenge-weighted query batch. This proves only the recurrence's
closed form; it is not a refinement theorem for any Rust implementation. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryAccumulator

open scoped BigOperators

structure State (K E : Type) [Field K] [Field E] where
  weights : Fin 64 → K
  rhs : E
  power : K
  next : Nat

def initial {K E : Type} [Field K] [Field E] : State K E :=
  { weights := fun _ => 0, rhs := 0, power := 1, next := 0 }

/-- Add one queried value and its K-valued basis column, then advance the
challenge power and query index. -/
def step {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (s : State K E) : State K E :=
  { weights := fun j => s.weights j + s.power * basis s.next j
    rhs := s.rhs + iota s.power * values s.next
    power := s.power * rho
    next := s.next + 1 }

/-- Run `n` recurrence steps over the indexed value and basis sequences. -/
def run {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) : Nat → State K E
  | 0 => initial
  | n + 1 => step iota rho values basis (run iota rho values basis n)

/-- The accumulator's four fields have the expected geometric-sum closed
forms after any number of recurrence steps. -/
theorem run_closed_forms {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (n : Nat) :
    (run iota rho values basis n).power = rho ^ n ∧
    (run iota rho values basis n).next = n ∧
    (∀ j : Fin 64,
      (run iota rho values basis n).weights j =
        ∑ i ∈ Finset.range n, rho ^ i * basis i j) ∧
    (run iota rho values basis n).rhs =
      ∑ i ∈ Finset.range n, (iota rho) ^ i * values i := by
  induction n with
  | zero =>
      simp [run, initial]
  | succ n ih =>
      rcases ih with ⟨hpower, hnext, hweights, hrhs⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (run iota rho values basis n).power * rho = rho ^ (n + 1)
        rw [hpower, pow_succ]
      · change (run iota rho values basis n).next + 1 = n + 1
        rw [hnext]
      · intro j
        change (run iota rho values basis n).weights j +
            (run iota rho values basis n).power *
              basis (run iota rho values basis n).next j = _
        rw [hweights j, hpower, hnext, Finset.sum_range_succ]
      · change (run iota rho values basis n).rhs +
            iota ((run iota rho values basis n).power) *
              values (run iota rho values basis n).next = _
        rw [hrhs, hpower, hnext, map_pow, Finset.sum_range_succ]

theorem run_power {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (n : Nat) :
    (run iota rho values basis n).power = rho ^ n :=
  (run_closed_forms iota rho values basis n).1

theorem run_next {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (n : Nat) :
    (run iota rho values basis n).next = n :=
  (run_closed_forms iota rho values basis n).2.1

theorem run_weights {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (n : Nat) (j : Fin 64) :
    (run iota rho values basis n).weights j =
      ∑ i ∈ Finset.range n, rho ^ i * basis i j :=
  (run_closed_forms iota rho values basis n).2.2.1 j

theorem run_rhs {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Nat → E)
    (basis : Nat → Fin 64 → K) (n : Nat) :
    (run iota rho values basis n).rhs =
      ∑ i ∈ Finset.range n, (iota rho) ^ i * values i :=
  (run_closed_forms iota rho values basis n).2.2.2

/-- Repeat a finite 22-entry vector periodically when the accumulator uses a
natural-number index. -/
def extend22 {T : Type} (v : Fin 22 → T) (i : Nat) : T :=
  v ⟨i % 22, Nat.mod_lt _ (by decide)⟩

/-- The verifier-shaped fixed 22-step instance of the symbolic recurrence. -/
def run22 {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) : State K E :=
  run iota rho (extend22 values) (extend22 basis) 22

theorem run22_closed_forms {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) :
    (run22 iota rho values basis).next = 22 ∧
    (run22 iota rho values basis).power = rho ^ 22 ∧
    (∀ j : Fin 64,
      (run22 iota rho values basis).weights j =
        ∑ i : Fin 22, rho ^ i.val * basis i j) ∧
    (run22 iota rho values basis).rhs =
      ∑ i : Fin 22, (iota rho) ^ i.val * values i := by
  have h := run_closed_forms iota rho (extend22 values) (extend22 basis) 22
  rcases h with ⟨hpower, hnext, hweights, hrhs⟩
  refine ⟨hnext, hpower, ?_, ?_⟩
  · intro j
    change (run iota rho (extend22 values) (extend22 basis) 22).weights j =
      ∑ i : Fin 22, rho ^ i.val * basis i j
    calc
      (run iota rho (extend22 values) (extend22 basis) 22).weights j =
          ∑ i ∈ Finset.range 22, rho ^ i * extend22 basis i j := hweights j
      _ =
          ∑ i : Fin 22, rho ^ i.val * basis i j := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun i : Nat => rho ^ i * extend22 basis i j) 22]
        apply Finset.sum_congr rfl
        intro i _
        simp [extend22, Nat.mod_eq_of_lt i.isLt]
  · change (run iota rho (extend22 values) (extend22 basis) 22).rhs =
      ∑ i : Fin 22, (iota rho) ^ i.val * values i
    calc
      (run iota rho (extend22 values) (extend22 basis) 22).rhs =
          ∑ i ∈ Finset.range 22, (iota rho) ^ i * extend22 values i := hrhs
      _ =
          ∑ i : Fin 22, (iota rho) ^ i.val * values i := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun i : Nat => (iota rho) ^ i * extend22 values i) 22]
        apply Finset.sum_congr rfl
        intro i _
        simp [extend22, Nat.mod_eq_of_lt i.isLt]

theorem run22_next {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) :
    (run22 iota rho values basis).next = 22 :=
  (run22_closed_forms iota rho values basis).1

theorem run22_power {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) :
    (run22 iota rho values basis).power = rho ^ 22 :=
  (run22_closed_forms iota rho values basis).2.1

theorem run22_weights {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) (j : Fin 64) :
    (run22 iota rho values basis).weights j =
      ∑ i : Fin 22, rho ^ i.val * basis i j :=
  (run22_closed_forms iota rho values basis).2.2.1 j

theorem run22_rhs {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (rho : K) (values : Fin 22 → E)
    (basis : Fin 22 → Fin 64 → K) :
    (run22 iota rho values basis).rhs =
      ∑ i : Fin 22, (iota rho) ^ i.val * values i :=
  (run22_closed_forms iota rho values basis).2.2.2

#print axioms run_closed_forms
#print axioms run_power
#print axioms run_next
#print axioms run_weights
#print axioms run_rhs
#print axioms run22_closed_forms
#print axioms run22_next
#print axioms run22_power
#print axioms run22_weights
#print axioms run22_rhs

end AspisR1.QueryAccumulator
end

import R1Z.PV_RW_CompressStep
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressBound
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

-- Zero fuel represents failure to cover a control evaluation, not a stub
-- for an arithmetic operation. Sufficient fuel is proved below.
def bounded (step : M → (Q × Q) → Result (Q × Q)) :
    Nat → List M → (Q × Q) → Result (Q × Q)
  | 0, _, _ => .div
  | _+1, [], state => ok state
  | fuel+1, value::values, state => do
    let next ← step value state
    bounded step fuel values next

theorem sufficient (step : M → (Q × Q) → Result (Q × Q))
    (values : List M) (fuel : Nat) (bound : values.length < fuel)
    (state : Q × Q) : bounded step fuel values state = PV_RW_CompressStep.run step values state := by
  induction values generalizing fuel state with
  | nil =>
    cases fuel with
    | zero => simp only [List.length_nil] at bound; omega
    | succ fuel => rfl
  | cons value values ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [bounded,PV_RW_CompressStep.run]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro next _
      apply ih
      simp only [List.length_cons] at bound
      omega

theorem arity16 (lambda : Q) (values : List M) (shape : values.length=16)
    (state : Q × Q) :
    bounded (PV_RW_CompressStep.shipped lambda) 17 values state =
      PV_CompressList.stateFold values lambda state := by
  rw [sufficient _ values 17 (by omega),PV_RW_CompressStep.shipped_fold]

theorem prefix_steps (consumed : Nat) (bound : consumed ≤ 16) :
    consumed < 17 ∧ (consumed < 16 → consumed+1 ≤ 16) := by omega

-- Straight-line arithmetic has zero user loop iterations. The iterator
-- harness has at most 16 prefix iterations and one final next/termination
-- observation. Its bound18 exceeds that count; unwinding assertions remain on.
theorem iterator_bound (consumed : Nat) (bound : consumed ≤ 16) :
    consumed+1 < 18 := by omega
#print axioms sufficient
#print axioms arity16
#print axioms prefix_steps
#print axioms iterator_bound
end R1Z.PV_RW_CompressBound

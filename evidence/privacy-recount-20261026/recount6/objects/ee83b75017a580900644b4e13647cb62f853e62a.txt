import R1Z.PV_CompressModel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressStep
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

-- Exact operation sequence in logup.rs, retaining every Result branch.
def shipped (lambda : Q) (value : M) (state : Q × Q) : Result (Q × Q) := do
  let scaled ← aspis_core.field.QM31.mul_m31 state.2 value
  let out ← aspis_core.field.QM31.add state.1 scaled
  let power ← aspis_core.field.QM31.mul state.2 lambda
  ok (out,power)

def owned (lambda : Q) (value : M) (state : Q × Q) : Result (Q × Q) := do
  let scaled ← aspis_core.field.QM31.mul_m31 state.2 value
  let out ← aspis_core.field.QM31.add state.1 scaled
  let power ← aspis_core.field.QM31.mul state.2 lambda
  ok (out,power)

theorem step_eq (lambda : Q) (value : M) (state : Q × Q) :
    shipped lambda value state = owned lambda value state := rfl

-- Each recursive call consumes exactly one input and preserves order.
def run (step : M → (Q × Q) → Result (Q × Q)) :
    List M → (Q × Q) → Result (Q × Q)
  | [], state => ok state
  | value::values, state => do
    let next ← step value state
    run step values next

theorem run_congr (left right : M → (Q × Q) → Result (Q × Q))
    (step : ∀ value state, left value state = right value state)
    (values : List M) (state : Q × Q) :
    run left values state = run right values state := by
  induction values generalizing state with
  | nil => rfl
  | cons value values ih =>
    simp only [run,step]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

theorem run_eq (lambda : Q) (values : List M) (state : Q × Q) :
    run (shipped lambda) values state = run (owned lambda) values state :=
  run_congr _ _ (step_eq lambda) values state

theorem owned_fold (lambda : Q) (values : List M) (state : Q × Q) :
    run (owned lambda) values state = PV_CompressList.stateFold values lambda state := by
  induction values generalizing state with
  | nil => rfl
  | cons value values ih =>
    rcases state with ⟨out,power⟩
    simp only [run,owned,PV_CompressList.stateFold,bind_assoc_eq,bind_tc_ok]
    repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    exact ih _

-- This is a source-step model theorem; native iterator/step association must
-- be certified separately before it can justify a live op223 installation.
theorem shipped_fold (lambda : Q) (values : List M) (state : Q × Q) :
    run (shipped lambda) values state = PV_CompressList.stateFold values lambda state :=
  (run_eq lambda values state).trans (owned_fold lambda values state)
#print axioms step_eq
#print axioms run_congr
#print axioms run_eq
#print axioms owned_fold
#print axioms shipped_fold
end R1Z.PV_RW_CompressStep

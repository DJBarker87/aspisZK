import Hiq_RuntimeWriter
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeAction
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry

/-- Ledger projection of transactions. Foreign writes carry only the runtime
ownership check; verifier calls use the actual source writer. A rejected call
or a source reader has no account-data effect. Oracle effects are NOT erased
from the account security experiment by this separate ledger projection. -/
inductive Action where
  | invoke (layout : Layout) (data : Slice U8)
  | foreign (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell)
  | rollback

def apply (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program) (store : Store) :
    Action → Store × S2X.AccountEvent
  | .rollback => (store,.rollback)
  | .invoke layout data =>
    match Hiq_ReleaseRoute.route data with
    | .first => Hiq_RuntimeWriter.apply ops id store layout data
    | .second | .reject => (store,.rollback)
  | .foreign caller key value => by
    classical
    exact if caller ≠ id ∧ (store key).owner = caller then
      (put store key value,.committedWrite key (MultiproofConeCanonical.bytesOf value.data.val))
    else (store,.rollback)

theorem classified (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (action : Action) :
    Step ops id store (apply ops id store action).2 (apply ops id store action).1 := by
  classical
  cases action with
  | rollback => exact Step.rollback store
  | invoke layout data =>
    simp only [apply]
    cases Hiq_ReleaseRoute.route data with
    | first => exact Hiq_RuntimeWriter.classified ops keyLaw id store layout data
    | second => exact Step.rollback store
    | reject => exact Step.rollback store
  | foreign caller key value =>
    by_cases h : caller ≠ id ∧ (store key).owner = caller
    · simpa only [apply,if_pos h] using Step.foreign store key caller value h.1 h.2
    · simpa only [apply,if_neg h] using (Step.rollback store : Step ops id store .rollback store)

#print axioms classified
end AspisR1.Hiq_RuntimeAction
end

import Hiq_NativeWriter
import Hiq_RuntimeAction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeAction
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry

inductive Action (A : Type) where
  | invoke (layout : Layout) (data : Slice U8) (state : A)
  | foreign (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell)
  | rollback

def apply {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : S2W_D189Wrappers.Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store) :
    Action A → Store × S2X.AccountEvent
  | .invoke layout data state =>
    match Hiq_ReleaseRoute.route data with
    | .first => Hiq_NativeWriter.apply native copy allocator id store layout data state
    | .second | .reject => (store,.rollback)
  | .foreign caller key value => by
    classical
    exact if caller ≠ id ∧ (store key).owner = caller then
      (Hist_Store.put store key value,.committedWrite key (MultiproofConeCanonical.bytesOf value.data.val))
    else (store,.rollback)
  | .rollback => (store,.rollback)

/-- Foreign writes are independent of any verifier callback. -/
theorem foreign_eq {A : Type} (native : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : S2W_D189Wrappers.Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (ops : AdapterRw.Ops) (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell) :
    apply native copy allocator id store (.foreign caller key value) =
      Hiq_RuntimeAction.apply ops id store (.foreign caller key value) := rfl

#print axioms foreign_eq
end AspisR1.Hiq_NativeAction
end

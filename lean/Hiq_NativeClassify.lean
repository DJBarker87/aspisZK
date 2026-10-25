import Hiq_NativeAction
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_NativeClassify
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry S2Trust S2W_D189Entry S2W_D189Wrappers
open Hiq_NativeAction

theorem step {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (native : S2W_ExtractionBoundary.First)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (action : Action A) :
    Step ops id store (apply native copy allocator id store action).2
      (apply native copy allocator id store action).1 := by
  cases action with
  | invoke layout data state =>
    simp only [apply]
    cases Hiq_ReleaseRoute.route data with
    | first => exact Hiq_NativeWriter.classified ops law native source copy trustedCopy allocator id store layout data state
    | second => exact Step.rollback store
    | reject => exact Step.rollback store
  | rollback => exact Step.rollback store
  | foreign caller key value =>
    rw [Hiq_NativeAction.foreign_eq native copy allocator id store ops caller key value]
    exact Hiq_RuntimeAction.classified ops law id store (.foreign caller key value)

#print axioms step
end AspisR1.Hiq_NativeClassify
end

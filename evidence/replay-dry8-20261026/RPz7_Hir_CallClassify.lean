import RPz7_Hir_CallSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CallClassify
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers GExq_AccountExperiment Hir_Call

theorem classified {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data,
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = native1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (trustedCopy : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (store : Store) (call : Call A) :
    Step ops id store (native native1 native2 copy allocator id store call).2.1
      (native native1 native2 copy allocator id store call).1 := by
  unfold native
  cases route : Hiq_ReleaseRoute.route call.data with
  | reject => exact Step.rollback store
  | second => exact Step.rollback store
  | first =>
    have old := Hiq_NativeWriter.classified ops law native1 source copy trustedCopy allocator
      id store call.layout call.data call.state
    unfold Hiq_NativeWriter.apply at old
    unfold firstEffect
    cases reply : first native1 copy allocator (load store call.layout) id call.data call.state with
    | fail e => simpa only [reply] using old
    | div => simpa only [reply] using old
    | ok result => cases result with
      | Err e => simpa only [reply] using old
      | Ok value => rcases value with ⟨saved,post,final⟩; simpa only [reply] using old

#print axioms classified
end AspisR1.Hir_CallClassify
end

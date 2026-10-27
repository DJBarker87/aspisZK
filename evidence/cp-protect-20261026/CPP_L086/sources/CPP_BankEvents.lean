import CPP_BankHistory
import Hist_Persistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankEvents
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
attribute [local instance] Classical.propDecidable

theorem step_effect {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program) (bank : Bank) (action : Action A) :
    byteLedger (CPP_BankState.apply n1 n2 copy allocator id bank action).1.cells =
      S2X.applyEvent (byteLedger bank.cells) (CPP_BankState.apply n1 n2 copy allocator id bank action).2 := by
  cases action with
  | rollback => rfl
  | credit address amount => rfl
  | invoke input =>
    exact Hist_Persistence.step_effect ops id _ _ _
      (CPP_Classify.classified n1 n2 copy allocator id bank.cells (invocation bank input) ops law source std)
  | foreign caller address value coins =>
    unfold CPP_BankState.apply
    split
    · funext key
      by_cases same : key = address <;> simp [byteLedger,Hist_Store.put,S2X.applyEvent,same]
    · rfl
  | reap address =>
    unfold CPP_BankState.apply
    split
    · funext key
      by_cases same : key = address <;> simp [byteLedger,Hist_Store.put,S2X.applyEvent,same,absent,MultiproofConeCanonical.bytesOf]
    · rfl

#print axioms step_effect
end AspisR1.CPP_BankEvents
end

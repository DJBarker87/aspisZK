import CPP_BankEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankBinding
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPP_BankHistory
variable {A : Type} (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)

include ops law source std

theorem history_effect (bank : Bank) (actions : List (Action A)) :
    byteLedger (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1.cells =
      S2X.history (byteLedger bank.cells) (CPP_BankHistory.run n1 n2 copy allocator id bank actions).2 := by
  induction actions generalizing bank with
  | nil => rfl
  | cons action rest ih =>
    simp only [CPP_BankHistory.run,S2X.history]
    rw [← CPP_BankEvents.step_effect ops law n1 n2 source copy std allocator id bank action]
    exact ih _

/-- Actual computed data/balance events, including credit and zero-lamport
cleanup cases, construct all three history fields. This source/runtime-model
constructor still requires the deployed executor's association with its actions. -/
def binding (bank : Bank) (actions : List (Action A)) (key : Nat)
    (atRest : CPP_BankFrame.AtRest bank)
    (owner : (bank.cells key).owner = id) (marker : Initialized (bank.cells key).data) :
    S2X.CheckpointVersionBinding (byteLedger bank.cells key)
      (byteLedger (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1.cells key) where
  key := key
  ledger := byteLedger bank.cells
  events := (CPP_BankHistory.run n1 n2 copy allocator id bank actions).2
  savedAtCommit := rfl
  loadedAtEntry := congrFun (history_effect ops law n1 n2 source copy std allocator id bank actions) key
  noInterveningWrite := (CPP_BankHistory.protection ops law n1 n2 source copy std allocator id bank actions key
    owner marker (CPP_BankFrame.initial_positive bank key atRest marker)).1

#print axioms history_effect
#print axioms binding
end AspisR1.CPP_BankBinding
end

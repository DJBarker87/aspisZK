import CPR_Persistence
import CPP_BankBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_AtomicBank
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_Persistence

/-- Parent settlement, applied once after all tentative actions. No CPI-level
cleanup or success-to-parent-success inference occurs in this definition. -/
def settle (before : Bank) (tentative : Bank × List S2X.AccountEvent)
    (success : Bool) : Bank × List S2X.AccountEvent :=
  if success then tentative else (before,[.rollback])

def run {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (before : Bank) (actions : List (Action A)) (success : Bool) : Bank × List S2X.AccountEvent :=
  settle before (CPP_BankHistory.run n1 n2 copy allocator id before actions) success

variable {A : Type} (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)

include ops keyLaw source std

theorem effect (before : Bank) (actions : List (Action A)) (success : Bool) :
    byteLedger (run n1 n2 copy allocator id before actions success).1.cells =
      S2X.history (byteLedger before.cells) (run n1 n2 copy allocator id before actions success).2 := by
  cases success with
  | false => rfl
  | true => exact CPP_BankBinding.history_effect ops keyLaw n1 n2 source copy std allocator id before actions

theorem protected (before : Bank) (actions : List (Action A)) (success : Bool) (key : Nat)
    (owner : (before.cells key).owner = id) (marker : Initialized (before.cells key).data)
    (positive : 0 < before.lamports key) :
    (∀ event ∈ (run n1 n2 copy allocator id before actions success).2, S2X.Preserves key event) ∧
      (run n1 n2 copy allocator id before actions success).1.cells key = before.cells key ∧
      before.lamports key ≤ (run n1 n2 copy allocator id before actions success).1.lamports key := by
  cases success with
  | false =>
    refine ⟨?_,rfl,le_rfl⟩
    intro e member
    have same : e = .rollback := List.mem_singleton.mp member
    subst e
    exact True.intro
  | true => exact CPP_BankHistory.protection ops keyLaw n1 n2 source copy std allocator id before actions key owner marker positive

/-- Constructs history fields from computed committed-parent events, including
rollback. Deployment association is supplied later only by the two-TX law. -/
def binding (before : Bank) (actions : List (Action A)) (success : Bool) (key : Nat)
    (owner : (before.cells key).owner = id) (marker : Initialized (before.cells key).data)
    (positive : 0 < before.lamports key) :
    S2X.CheckpointVersionBinding (byteLedger before.cells key)
      (byteLedger (run n1 n2 copy allocator id before actions success).1.cells key) where
  key := key
  ledger := byteLedger before.cells
  events := (run n1 n2 copy allocator id before actions success).2
  savedAtCommit := rfl
  loadedAtEntry := congrFun (effect ops keyLaw n1 n2 source copy std allocator id before actions success) key
  noInterveningWrite := (protected ops keyLaw n1 n2 source copy std allocator id before actions success key owner marker positive).1

#print axioms effect
#print axioms protected
#print axioms binding
end AspisR1.CPR_AtomicBank
end

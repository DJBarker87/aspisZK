import CPP_Classify
import CPP_BankSourceLoad
import Hir_ProvenanceModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankState
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_ProvenanceModel CPP_Invocation
attribute [local instance] Classical.propDecidable

/-- A local data/balance runtime projection. Native invocations use the
source count guards and actual complete wrapper reply. This projection's
association with a deployed bank/transaction executor is still a proof gate. -/
structure Bank where
  cells : Store
  lamports : Nat → Nat

inductive Action (A : Type) where
  | invoke (input : Invocation A)
  | foreign (caller : S2W_ExtractionBoundary.Program) (key : Nat) (value : Cell) (lamports : Nat)
  | credit (key amount : Nat)
  | reap (key : Nat)
  | rollback

def layout (bank : Bank) (old : Layout) : Layout :=
  {old with records := fun cell => {old.records cell with lamports := bank.lamports cell}}

def invocation {A : Type} (bank : Bank) (input : Invocation A) : Invocation A :=
  {input with call := {input.call with layout := layout bank input.call.layout}}

def absent : Cell := ⟨Hist_Nonvacuity.key 0#u8,⟨[],by simp⟩⟩

def apply {A : Type} (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (bank : Bank) :
    Action A → Bank × S2X.AccountEvent
  | .invoke input =>
    let effect := CPP_Invocation.native n1 n2 copy allocator id bank.cells (invocation bank input)
    (⟨effect.1,bank.lamports⟩,effect.2.1)
  | .foreign caller key value coins =>
    if caller ≠ id ∧ (bank.cells key).owner = caller ∧
        (value.owner = caller ∨ Zero value.data) then
      (⟨Hist_Store.put bank.cells key value,S2Trust.put bank.lamports key coins⟩,
        .committedWrite key (MultiproofConeCanonical.bytesOf value.data.val))
    else (bank,.rollback)
  | .credit key amount =>
    (⟨bank.cells,S2Trust.put bank.lamports key (bank.lamports key + amount)⟩,.rollback)
  | .reap key =>
    if bank.lamports key = 0 then
      (⟨Hist_Store.put bank.cells key absent,bank.lamports⟩,.committedWrite key [])
    else (bank,.rollback)
  | .rollback => (bank,.rollback)

/-- The source record used by native invocation reads the SAME bank balance.
Other initial metadata/alias/ABI admission remains the existing runtime gate. -/
theorem entry_balance (bank : Bank) (old : Layout) (cell : Nat) :
    ((load bank.cells (layout bank old)).records cell).lamports = bank.lamports cell := rfl

#print axioms entry_balance
end AspisR1.CPP_BankState
end

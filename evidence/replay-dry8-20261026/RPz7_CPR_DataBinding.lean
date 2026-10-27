import RPz7_CPR_DataPersistence
import RPz7_CPR_AtomicBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_DataBinding
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_DataPersistence
open AspisV8R19.DuplexFrames MultiproofConeCanonical

variable {A Tx Key : Type}
    (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)
    (bank : Bank) (actions : List (Action A)) (key : Nat)
    (owner : (bank.cells key).owner = id) (marker : Initialized (bank.cells key).data)
    (positive : 0 < bank.lamports key)
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Bytes)
    (law : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (physicalKey : Key) (adjacent : next t u) (eligible : ordinary t physicalKey)
    (tentativeView : tentative t physicalKey = snapshot (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1 key)
    (status : success t = true)

include keyLaw source std owner marker positive law adjacent eligible tentativeView status

theorem next_load :
    loaded u physicalKey = some (byteLedger (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1.cells key) := by
  rw [law t u adjacent physicalKey eligible,status,tentativeView]
  apply if_neg
  have frame := CPP_BankHistory.protection ops keyLaw n1 n2 source copy std allocator id bank actions key owner marker positive
  change (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1.lamports key ≠ 0
  omega

def binding (e2 : Entry)
    (entryView : loaded u physicalKey = some (bytesOf (e2.buffers (e2.handles 6).1).val)) :
    S2X.CheckpointVersionBinding (byteLedger bank.cells key)
      (bytesOf (e2.buffers (e2.handles 6).1).val) := by
  let version := CPR_AtomicBank.binding ops keyLaw n1 n2 source copy std allocator id bank actions true key owner marker positive
  have observed := Option.some.inj (entryView.symm.trans
    (next_load ops keyLaw n1 n2 source copy std allocator id bank actions key owner marker positive
      next ordinary before tentative success loaded law t u physicalKey adjacent eligible tentativeView status))
  exact ⟨key,version.ledger,version.events,version.savedAtCommit,
    observed.trans version.loadedAtEntry,version.noInterveningWrite⟩

#print axioms next_load
#print axioms binding
end AspisR1.CPR_DataBinding
end

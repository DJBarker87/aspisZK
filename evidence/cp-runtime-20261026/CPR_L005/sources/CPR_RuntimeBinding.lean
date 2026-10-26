import CPR_AtomicBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_RuntimeBinding
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_Persistence

variable {A Tx Key : Type}
    (ops : AdapterRw.Ops) (keyLaw : ops.op36 = Hist_Authority.keyEq)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (source : ∀ id accounts data, AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts data = n1 id accounts data)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (id : S2W_ExtractionBoundary.Program)
    (bank : Bank) (actions : List (Action A)) (committed : Bool) (key : Nat)
    (owner : (bank.cells key).owner = id) (marker : Initialized (bank.cells key).data)
    (positive : 0 < bank.lamports key)
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Image)
    (law : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (physicalKey : Key) (adjacent : next t u) (eligible : ordinary t physicalKey)
    (beforeView : before t physicalKey = snapshot bank key)
    (tentativeView : tentative t physicalKey = snapshot (CPP_BankHistory.run n1 n2 copy allocator id bank actions).1 key)
    (status : success t = committed)

include keyLaw source std owner marker positive law adjacent eligible beforeView tentativeView status

theorem next_load :
    loaded u physicalKey = some (snapshot (CPR_AtomicBank.run n1 n2 copy allocator id bank actions committed).1 key) := by
  rw [law t u adjacent physicalKey eligible,status,beforeView,tentativeView]
  have frame := CPR_AtomicBank.protection ops keyLaw n1 n2 source copy std allocator id bank actions committed key owner marker positive
  have live : (snapshot (CPR_AtomicBank.run n1 n2 copy allocator id bank actions committed).1 key).lamports ≠ 0 := by
    change (CPR_AtomicBank.run n1 n2 copy allocator id bank actions committed).1.lamports key ≠ 0
    omega
  cases committed <;> exact if_neg live

/-- The entry-buffer interpretation is explicit and local to the physical
account actually loaded. No equality with saved bytes or desired history is
assumed by this interpretation. All history fields are computed here. -/
def binding (e2 : Entry)
    (entryView : ∀ image, loaded u physicalKey = some image →
      (e2.buffers (e2.handles 6).1).val = image.cell.data.val) :
    S2X.CheckpointVersionBinding (byteLedger bank.cells key)
      (MultiproofConeCanonical.bytesOf (e2.buffers (e2.handles 6).1).val) := by
  let version := CPR_AtomicBank.binding ops keyLaw n1 n2 source copy std allocator id bank actions committed key owner marker positive
  have observed := entryView _ (next_load ops keyLaw n1 n2 source copy std allocator id bank actions committed key owner marker positive
    next ordinary before tentative success loaded law t u physicalKey adjacent eligible beforeView tentativeView status)
  exact ⟨key,version.ledger,version.events,version.savedAtCommit,
    (congrArg MultiproofConeCanonical.bytesOf observed).trans version.loadedAtEntry,version.noInterveningWrite⟩

#print axioms next_load
#print axioms binding
end AspisR1.CPR_RuntimeBinding
end

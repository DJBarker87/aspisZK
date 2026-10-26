import CPR_Persistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_DataPersistence
open AspisV8R19.DuplexFrames
open Hist_Store CPP_BankState MultiproofConeCanonical

/-- Only the observable account-data projection and the zero-account test.
This is intentionally weaker than equality of owner/balance/account records. -/
structure Image where
  data : Bytes
  lamports : Nat

def snapshot (bank : Bank) (key : Nat) : Image :=
  ⟨byteLedger bank.cells key,bank.lamports key⟩

def visible (image : Image) : Option Bytes :=
  if image.lamports = 0 then none else some image.data

/-- Minimal proposed runtime law. The ordinary-key restriction excludes fee
payer and durable nonce rollback effects. No caller, hash, history, key pairing,
source acceptance, source execution equality or security conclusion appears. -/
def TwoTransactionLaw {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Bytes) : Prop :=
  ∀ t u, next t u → ∀ key, ordinary t key →
    loaded u key = visible (if success t then tentative t key else before t key)

def project (image : CPR_Persistence.Image) : Image :=
  ⟨bytesOf image.cell.data.val,image.lamports⟩

theorem visible_projection (image : CPR_Persistence.Image) :
    visible (project image) =
      (CPR_Persistence.visible image).map (fun a => bytesOf a.cell.data.val) := by
  by_cases zero : image.lamports = 0
  · simp only [visible,project,zero,↓reduceIte,CPR_Persistence.visible,Option.map_none]
  · simp only [visible,project,zero,↓reduceIte,CPR_Persistence.visible,Option.map_some]

/-- The original full-image candidate implies this strictly smaller observed
claim. The narrower law is the one proposed for owner consideration. -/
theorem of_full {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → CPR_Persistence.Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option CPR_Persistence.Image)
    (law : CPR_Persistence.TwoTransactionLaw next ordinary before tentative success loaded) :
    TwoTransactionLaw next ordinary (fun t k => project (before t k))
      (fun t k => project (tentative t k)) success
      (fun t k => (loaded t k).map (fun a => bytesOf a.cell.data.val)) := by
  intro t u adjacent key eligible
  change (loaded u key).map (fun a : CPR_Persistence.Image => bytesOf a.cell.data.val) =
    visible (if success t then project (tentative t key) else project (before t key))
  rw [law t u adjacent key eligible]
  cases h : success t <;> exact (visible_projection _).symm

#print axioms visible_projection
#print axioms of_full
end AspisR1.CPR_DataPersistence
end

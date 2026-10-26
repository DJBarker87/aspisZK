import CPP_BankState
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_Persistence
open Aeneas Aeneas.Std Result Hist_Store CPP_BankState

/-- Physical account contents only: no invocation-specific privileges or borrow tokens. -/
structure Image where
  cell : Cell
  lamports : Nat

def visible (image : Image) : Option Image :=
  if image.lamports = 0 then none else some image

def snapshot (bank : Bank) (key : Nat) : Image := ⟨bank.cells key,bank.lamports key⟩

/-- Proposed operational law, NOT adopted trust. `next` means consecutive loads
on the same bank lineage with no intervening transaction; `ordinary` excludes
fee-payer/durable-nonce rollback special cases. `tentative` is the final parent
transaction image, not the image at a successful CPI. Physical keys are shared
by the two observations. Cleanup occurs only at this transaction boundary. -/
def TwoTransactionLaw {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Image) : Prop :=
  ∀ t u, next t u → ∀ key, ordinary t key →
    loaded u key = visible (if success t then tentative t key else before t key)

theorem successful_load {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Image)
    (law : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
    (committed : success t = true) (live : (tentative t key).lamports ≠ 0) :
    loaded u key = some (tentative t key) := by
  rw [law t u adjacent key eligible,committed]
  exact if_neg live

theorem failed_load {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Image)
    (law : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
    (failed : success t = false) :
    loaded u key = visible (before t key) := by
  simpa only [failed,Bool.false_eq_true,↓reduceIte] using law t u adjacent key eligible

theorem zero_cleanup (image : Image) (zero : image.lamports = 0) :
    visible image = none := if_pos zero

theorem loaded_image (image value : Image) (loaded : visible image = some value) :
    value = image ∧ 0 < value.lamports := by
  unfold visible at loaded
  split at loaded
  · cases loaded
  · have eq := Option.some.inj loaded
    subst value
    exact ⟨rfl,by omega⟩

#print axioms successful_load
#print axioms failed_load
#print axioms zero_cleanup
#print axioms loaded_image
end AspisR1.CPR_Persistence
end

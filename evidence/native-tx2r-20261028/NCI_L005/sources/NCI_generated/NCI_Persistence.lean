import CPR_DataPersistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_Persistence
open AspisR1.CPR_DataPersistence MultiproofConeCanonical
-- RuntimePersistence is the existing owner-approved trust item. The other
-- hypotheses describe the SAME account and committed TX1 output in the game.
theorem saved_loaded {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Bytes)
    (RuntimePersistence : TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
    (accepted : success t = true) (retained : (tentative t key).lamports ≠ 0)
    (saved : Bytes) (TX1SavedBytes : (tentative t key).data = saved) :
    loaded u key = some saved := by
  rw [RuntimePersistence t u adjacent key eligible]
  simp [accepted, visible, retained, TX1SavedBytes]
#print axioms saved_loaded
end AspisR1.NCI_Persistence

import NLW_Root0
import RPz7_CPR_DataPersistence
set_option autoImplicit false
noncomputable section
namespace NLW_Persistence
open Aeneas Aeneas.Std AspisR1
open AspisR1.CPR_DataPersistence
/-- RuntimePersistence transports only the successful ordinary-key DATA
projection. It does not assert root provenance or digest injectivity. -/
theorem loaded_success {Tx Key : Type} (next : Tx → Tx → Prop)
 (ordinary : Tx → Key → Prop) (before tentative : Tx → Key → Image)
 (success : Tx → Bool) (loaded : Tx → Key → Option AspisV8R19.DuplexFrames.Bytes)
 (law : TwoTransactionLaw next ordinary before tentative success loaded)
 (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
 (accepted : success t=true) (live : (tentative t key).lamports≠0) :
 loaded u key=some (tentative t key).data := by
 rw [law t u adjacent key eligible,accepted]
 simp only [Bool.true_eq,↓reduceIte,visible,live,↓reduceIte]
/-- The loaded checkpoint is the SAME saved data; no owner/balance/frame
identity is smuggled into this data-only runtime item. -/
theorem loaded_bytes {Tx Key : Type} (next : Tx → Tx → Prop)
 (ordinary : Tx → Key → Prop) (before tentative : Tx → Key → Image)
 (success : Tx → Bool) (loaded : Tx → Key → Option AspisV8R19.DuplexFrames.Bytes)
 (law : TwoTransactionLaw next ordinary before tentative success loaded)
 (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
 (accepted : success t=true) (live : (tentative t key).lamports≠0)
 (checkpoint : AspisV8R19.DuplexFrames.Bytes) (read : loaded u key=some checkpoint) :
 checkpoint=(tentative t key).data := by
 exact Option.some.inj (read.symm.trans
  (loaded_success next ordinary before tentative success loaded law t u key adjacent eligible accepted live))
#print loaded_success
#print loaded_bytes
#print axioms loaded_success
#print axioms loaded_bytes
end NLW_Persistence

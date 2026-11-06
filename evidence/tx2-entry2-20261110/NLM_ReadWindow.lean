import NLM_SnapshotBridge
import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NLM_ReadWindow
open Aeneas Aeneas.Std Result AdapterRw
abbrev Owned := r1_pool_adapter.owned.OwnedAccount
abbrev PE := solana_program_error.ProgramError
/-- Actual native K005/K006 scalar/one-byte assertion schema ONLY. At that
revision, other bytes were zero-initialized. It is not promoted to a universal
arbitrary-buffer cut; the stronger initializer calibration is separate. -/
def Window (before after : Slice U8) (i : Nat) : Prop :=
 after.val.length=before.val.length ∧
 (i<before.val.length → after.val[i]?=before.val[i]?)
/-- Symbolic extensionality for an arbitrary prestate. The enclosing native
fold still must establish the window family on THAT actual vector. -/
theorem all_windows (before after : Slice U8)
 (windows : ∀ i,Window before after i) : after=before := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact (windows 0).1
 · intro i hi hj
   have same := (windows i).2 hj
   simpa [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using same
#print all_windows
#print axioms all_windows
end NLM_ReadWindow

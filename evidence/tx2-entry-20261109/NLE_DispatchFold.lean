import NLE_DispatchState
set_option autoImplicit false
noncomputable section
namespace NLE_Dispatch
open Aeneas Aeneas.Std Result AspisR1
/-- Per-occurrence head/copy state association, then the predecessor's complete
ordered fallback tree. No route or child success is assumed. -/
theorem source {Account : Type} (ops : NIV_RawBoundary.Boundaries Account)
 (state : State Account) : (G ops state).2 =
 NIV_RawBoundary.process ops state.program state.accounts state.data := by
 change (NJD_EntrySpine.process ops state.program state.accounts state.data).2 = _
 exact NJD_EntrySpine.process_erasure ops state.program state.accounts state.data
/-- The native/profile boundary is explicit; arbitrary lifecycle children are
not silently erased from the unrestricted process function. -/
theorem emitted {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
 (state : State Account) : (G (NIV_RawBoundary.profile ops) state).2 =
 NIV_ExtractedForward.process ops state.program state.accounts state.data := by
 rw [source]
 exact NIV_RawBoundary.process_profile ops state.program state.accounts state.data
#print source
#print emitted
#print axioms source
#print axioms emitted
end NLE_Dispatch

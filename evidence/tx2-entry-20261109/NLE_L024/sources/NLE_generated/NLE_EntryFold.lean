import NLE_DispatchFold
set_option autoImplicit false
noncomputable section
namespace NLE_Entry
open Aeneas Aeneas.Std Result AspisR1
abbrev State := NLE_Dispatch.State
abbrev Event := NLE_Dispatch.Event
abbrev PR := NLE_Dispatch.PR
abbrev Run := NLE_Dispatch.Run
/-- Actual deployed feature branch: admission precedes every account read and
process event. Every rejecting admission has no dispatch suffix. -/
def G {Account : Type} (ops : NIV_RawBoundary.Boundaries Account)
 (state : State Account) : Run Account PR :=
 NJD_Trace.bind (NJD_Trace.call (.admission state.data) (ops.admitted state.data)) fun allowed =>
 if allowed then NLE_Dispatch.G ops state else NJD_Trace.pure (.Err .InvalidInstructionData)
theorem source {Account : Type} (ops : NIV_RawBoundary.Boundaries Account)
 (state : State Account) : (G ops state).2 =
 NIV_RawBoundary.entry ops state.program state.accounts state.data := by
 change (NJD_EntrySpine.entry ops state.program state.accounts state.data).2 = _
 exact NJD_EntrySpine.entry_erasure ops state.program state.accounts state.data
theorem emitted {Account : Type} (ops : Hiq_DispatchSource.Ops Account)
 (state : State Account) : (G (NIV_RawBoundary.profile ops) state).2 =
 NIV_ExtractedForward.entry ops state.program state.accounts state.data := by
 change (NJD_EntrySpine.entry (NIV_RawBoundary.profile ops) state.program state.accounts state.data).2 = _
 exact NJD_EntrySpine.emitted ops state.program state.accounts state.data
/-- Exact local admission cut; no endpoint or child-success premise. -/
theorem rejected {Account : Type} (ops : NIV_RawBoundary.Boundaries Account)
 (state : State Account) (rejected : ops.admitted state.data = ok false) :
 G ops state = ([.admission state.data],ok (.Err .InvalidInstructionData)) := by
 unfold G
 rw [rejected]
 rfl
#print G
#print source
#print emitted
#print rejected
#print axioms source
#print axioms emitted
#print axioms rejected
end NLE_Entry

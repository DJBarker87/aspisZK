import NLC_Step_rootCopy
import NKQ_MaskLowStep
import NKQ_MaskHighStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- The low callback reads the claims held by THIS parent. The loop bound is
internal to from_fn; its native iteration association is still OPEN. -/
theorem low_callback {H : Type} (s : State H) (claims : Claims)
 (same : s.locals.claims = some claims) (i : Usize) (inside : i.val < 16) :
 (do let c ← read s.locals.claims
     (FinishModel.closureFn9 s.input.digest).call_mut c i) =
 ok (NKQ_MaskLowStep.lowAt claims i inside,claims) := by
 rw [same]
 simp only [read,bind_tc_ok]
 exact NKQ_MaskLowStep.step s.input.digest claims i inside

theorem high_callback {H : Type} (s : State H) (claims : Claims)
 (same : s.locals.claims = some claims) (i : Usize) (inside : i.val < 10) :
 (do let c ← read s.locals.claims
     (FinishModel.closureFn5 s.input.digest).call_mut c i) =
 ok (NKQ_MaskHighStep.highAt claims i inside,claims) := by
 rw [same]
 simp only [read,bind_tc_ok]
 exact NKQ_MaskHighStep.step s.input.digest claims i inside

def rootTry {H : Type} (s : State H) : Code (core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) := do
 let payload ← read s.locals.payload
 core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload

def rootUnwrap {H : Type} (s : State H)
 (attempt : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Code (Post H) := do
 let root ← (IDa_Deployed.boundaries s.input.reservation).unwrapRoot attempt
 pure (.inr (put s .verified {s.locals with root:=some root}))
/-- Separate try_into and unwrap occurrences in source evaluation order. -/
theorem root_occurrences {H : Type} (s : State H) (atSite : s.next = .rootCopy) :
 step s = (do let attempted ← rootTry s; rootUnwrap s attempted) := by
 rw [step_rootCopy s atSite]
 rfl
#print axioms low_callback
#print axioms high_callback
#print axioms root_occurrences
end AspisR1.NLC_Finish
end

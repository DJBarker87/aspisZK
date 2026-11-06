import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source dispatcher window only; no native/harness association is inferred. -/
def window_rootCopy {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 let payload ← read l.payload
 let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
 let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r
 pure (.inr (put s .verified {l with root:=some root}))
/-- Exact SAME-state source step. The native cut is not a hypothesis of this theorem. -/
theorem step_rootCopy {H : Type} (s : State H) (atSite : s.next = .rootCopy) :
 step s = window_rootCopy s := by
 rcases s with ⟨i,l,next⟩
 cases atSite
 rfl
#print axioms step_rootCopy
#print step_rootCopy
end AspisR1.NLC_Finish
end

import NLC_Step_rootCopy
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source input frame for every possible reply, with no successful-child premise.
This does not assert a physical native frame or a native cut producer. -/
theorem frame_rootCopy {H : Type} (s : State H) (atSite : s.next = .rootCopy) :
 AllLeaves (FramePost s) (step s) := by
 rw [step_rootCopy s atSite]
 unfold window_rootCopy
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | exact returned_frame s _ _ _
 | exact frame_put s _ _
 | exact frame_next s _
 | (change True; trivial)
 | split
#print axioms frame_rootCopy
#print frame_rootCopy
end AspisR1.NLC_Finish
end

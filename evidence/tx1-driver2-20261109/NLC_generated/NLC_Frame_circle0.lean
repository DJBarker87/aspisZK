import NLC_Step_circle0
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source input frame for every possible reply, with no successful-child premise.
This does not assert a physical native frame or a native cut producer. -/
theorem frame_circle0 {H : Type} (s : State H) (atSite : s.next = .circle0) :
 AllLeaves (FramePost s) (step s) := by
 rw [step_circle0 s atSite]
 unfold window_circle0
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | exact returned_frame s _ _ _
 | exact frame_put s _ _
 | exact frame_next s _
 | (change True; trivial)
 | split
#print axioms frame_circle0
#print frame_circle0
end AspisR1.NLC_Finish
end

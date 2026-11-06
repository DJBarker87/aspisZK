import NLC_Step_payload2
import NLC_FrameAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Source input frame for every possible reply, with no successful-child premise.
This does not assert a physical native frame or a native cut producer. -/
theorem frame_payload2 {H : Type} (s : State H) (atSite : s.next = .payload2) :
 AllLeaves (FramePost s) (step s) := by
 rw [step_payload2 s atSite]
 unfold window_payload2
 repeat' first
 | (apply all_bind; intro)
 | (change ∀ _, _; intro)
 | exact returned_frame s _ _ _
 | exact frame_put s _ _
 | exact frame_next s _
 | (change True; trivial)
 | split
#print axioms frame_payload2
#print frame_payload2
end AspisR1.NLC_Finish
end

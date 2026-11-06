import NLJ_ObservedDenote
import NLC_LeafSound
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Symbolic state invariants; neither claims native memory admission. -/
def FramePost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr t => Frame s t
def ProgressPost {H : Type} (s : State H) : Post H → Prop
 | .inl _ => True | .inr t => rank t < rank s
end AspisR1.NLJ_Observed
end

import XRo_Join_Installed
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRo_Join_Nonvacuity

def copyUnit : core.marker.Copy Unit := {cloneInst := {clone := fun u=>ok u}}
def failingDigest : E.D Unit := ⟨copyUnit,fun _ _=>.fail .panic⟩

/-- SAME concrete rejected initialization in emitted and adopted transcript. -/
theorem rejected_initialization :
 XRn_Join_Release.transcript.Transcript.new failingDigest () (Array.repeat 32#usize 0#u8) .S2 = .fail .panic ∧
 AspisR1PublicPreparation.transcript.Transcript.new (cd failingDigest) ()
   (Array.repeat 32#usize 0#u8) .S2 = .fail .panic := ⟨rfl,rfl⟩

#print axioms rejected_initialization
end XRo_Join_Nonvacuity

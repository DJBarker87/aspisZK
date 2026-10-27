import XRn_JoinedGeometry
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRn_JoinedNonvacuity

def copyUnit : core.marker.Copy Unit := {cloneInst := {clone := fun u=>ok u}}
def failingDigest : aspis_core.digest.Digest32 Unit := ⟨copyUnit,fun _ _=>.fail .panic⟩

/-- A concrete rejected initialization; no uninhabited abstract dictionary. -/
theorem rejected_initialization :
 transcript.Transcript.new failingDigest () (Array.repeat 32#usize 0#u8) .S2=.fail .panic := rfl

/-- The accessor transport has an actual successful inhabitant. This raw
geometry is not claimed to be the output of the inverse constructor. -/
theorem accessor : ∃ (g : verifier.QueryGeometry) (r : Array U32 5#usize),
 g.start=0#usize ∧ verifier.QueryGeometry.for_query g 0#usize=ok r ∧
 AspisR1.Port5Q1_GeometryBinding.forQuery (XRn_JoinedGeometry.cohort g) 0#usize=ok r := by
 let r := Array.repeat 5#usize 0#u32
 let g : verifier.QueryGeometry := ⟨0#usize,⟨[r],by decide⟩,⟨[0#u32],by decide⟩⟩
 have src : verifier.QueryGeometry.for_query g 0#usize=ok r := rfl
 exact ⟨g,r,rfl,src,(XRn_JoinedGeometry.for_query g 0#usize (by decide)).symm.trans src⟩

#print axioms rejected_initialization
#print axioms accessor
end XRn_JoinedNonvacuity

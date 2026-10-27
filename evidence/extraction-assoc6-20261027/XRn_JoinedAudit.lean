import XRn_JoinedDot
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
 let g : verifier.QueryGeometry := ⟨0#usize,⟨[r],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩,⟨[0#u32],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩⟩
 have src : verifier.QueryGeometry.for_query g 0#usize=ok r := rfl
 exact ⟨g,r,rfl,src,(XRn_JoinedGeometry.for_query g 0#usize (by decide)).symm.trans src⟩

#print axioms rejected_initialization
#print axioms accessor
end XRn_JoinedNonvacuity

#print axioms XRn_JoinedGeometry.cohort_emitted
#print axioms XRn_JoinedGeometry.emitted_cohort
#print axioms XRn_JoinedGeometry.for_query
#print axioms XRn_JoinedGeometry.reversed_range
#print axioms XRn_JoinedDot.reduce
#print axioms XRn_Join_Release.verifier.Prepared.new
#print axioms XRn_Join_Release.verifier.QueryGeometry.for_range
#print axioms XRn_Join_Release.verifier.candidate.tx1
#print axioms verifier.prepared_claim
#print axioms verifier.checkpoint

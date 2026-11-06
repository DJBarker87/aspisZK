import NLW_Root0
set_option autoImplicit false
noncomputable section
namespace NLW_DigestBoundary
open Aeneas Aeneas.Std AspisR1
/-- Byte-sequence equality needed for the checkpoint root follows either
from provenance or else leaves a concrete collision event. No injectivity
assumption is added to the SHA realization row. -/
def Collision {D : Type} (hash : List U8 → D) (a b : Slice U8) : Prop :=
 a.val≠b.val ∧ hash a.val=hash b.val
/-- Algebraic boundary only: install the actual resume digest check and
TX1 saved-root law before applying this to the entry spine. -/
theorem roots_or_collision {D : Type} (hash : List U8 → D)
 (checkpoint oldProof proof : Slice U8)
 (saved : NLW_Root0.Binds checkpoint oldProof)
 (checked : hash oldProof.val=hash proof.val) :
 NLW_Root0.Binds checkpoint proof ∨ Collision hash oldProof proof := by
 by_cases roots : NLW_Root0.Binds checkpoint proof
 · exact .inl roots
 · apply Or.inr
   refine ⟨?_,checked⟩
   intro same
   apply roots
   simpa only [NLW_Root0.Binds,same] using saved
#print Collision
#print roots_or_collision
#print axioms roots_or_collision
end NLW_DigestBoundary

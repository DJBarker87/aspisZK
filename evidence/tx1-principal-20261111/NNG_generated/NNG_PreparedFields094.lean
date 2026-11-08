import NNG_PreparedClaim094
import NNG_PreparedCopies094
import NNG_PreparedQueries094
import NHS_Fields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedFields094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Every checkpoint Prepared-field clause comes from its SAME source
producer and retained semantic input. All source-origin premises here are
internal reached-call facts, to be supplied by the parent call tree. -/
theorem reached (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (semantic : NNG_SemanticAt094.SemanticAt env input.1)
 (domain : LIBC_PreparedDomain.Domain input)
 (variant : input.2.1.variant=.S2)
 (alpha : ∀ q∈input.1.alpha.val,NHS_Fields.QCanonical q)
 (coordinates : ∀ z∈input.1.z.val,NHS_Fields.QCanonical z.x ∧ NHS_Fields.QCanonical z.y)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared p) := by
 have copies := NNG_PreparedCopies094.copied input env p g ev returned
 have fields := NNG_PreparedFacts094.canonical input env p g ev returned
 have queries := NNG_PreparedQueries094.returned input env p g ev returned
 apply NHS_Fields.transport p (copies.1.trans variant) queries.2 fields.1 fields.2.1
  fields.2.2.1 fields.2.2.2.1
 · rw [copies.2.2.1]
   exact alpha
 · rw [copies.2.2.2]
   exact coordinates
 · exact NNG_PreparedClaim094.canonical input env p g ev semantic domain returned
#print axioms reached
end AspisR1.NNG_PreparedFields094

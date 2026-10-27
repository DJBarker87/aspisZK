import XRr_SemanticCarriers
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRr_SemanticBlock
open XRr_SemanticCarriers
/-- Both row-order rejection and the three chronological digest requests use
identical arguments/replies. Overflow of tag/counter and fail/div are retained. -/
theorem source {H : Type} (D : C.D H) (s : C.ST H) (row : U8) (framed : Slice U8) :
 mapR (fun r => (inner id wire r.1,cst r.2))
 (r1_wire.SemanticTranscript.sample_block_validated (ed D) (est s) row framed)=
 AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated D s row framed := by
 unfold r1_wire.SemanticTranscript.sample_block_validated
 unfold AspisR1PublicPreparation.r1_wire.SemanticTranscript.sample_block_validated
 simp only [est,ed,mapR_bind,map_ok]
 split
 · rfl
 · simp only [mapR_bind,map_ok,lift,bind_tc_ok]
   rfl
#print axioms source
end XRr_SemanticBlock

import XRr_SemanticBlock
import XRo_Join_QmSampler
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRr_SemanticSample
open XRr_SemanticCarriers
theorem source {H : Type} (D : C.D H) (s : C.ST H) (r : CV) :
 mapR (fun p => (inner cq wire p.1,cst p.2))
 (r1_wire.SemanticTranscript.semantic_validated (ed D) (est s) (emittedRecord r))=
 AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated D s r := by
 unfold r1_wire.SemanticTranscript.semantic_validated
 unfold AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
 simp only [r1_wire.ValidatedRecord.impl.row,r1_wire.ValidatedRecord.impl.framed,
   AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.row,
   AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.framed,
   emittedRecord,bind_tc_ok,mapR_bind,map_ok]
 split
 · rfl
 · rw [← XRr_SemanticBlock.source D s r.row r.framed]
   cases h : r1_wire.SemanticTranscript.sample_block_validated (ed D) (est s) r.row r.framed with
   | fail e => rfl
   | div => rfl
   | ok pair =>
     rcases pair with ⟨result,after⟩
     cases result with
     | Err e => rfl
     | Ok block =>
       simp only [mapR_bind,bind_map,map_ok,inner,bind_tc_ok,
         core.result.Result.Insts.CoreOpsTry.branch]
       rw [←XRo_Join_QmSampler.sample]
       simp only [mapR_bind,bind_map,map_ok]
       rfl
#print axioms source
end XRr_SemanticSample

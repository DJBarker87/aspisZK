import XRy_QueryLaws
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
noncomputable section
namespace XRy_QueryTransport

theorem raw {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (inner id ce p.1,ct p.2))
   (XRn_Join_Release.transcript.Transcript.queries (ed D) (et t) row payload) =
 AspisR1PublicPreparation.QueriesModel.queries XRy_QueryLaws.rawBoundaries D t row payload := by
 unfold XRn_Join_Release.transcript.Transcript.queries AspisR1PublicPreparation.QueriesModel.queries
 rw [←XRo_Join_TranscriptBlock.absorb]
 simp only [mapR_bind,bind_map,map_ok,ct,ed,et,XRy_QueryLaws.rawBoundaries]
 repeat' (first | rfl | (congr 1) | funext)

#print axioms raw
#print prefix AspisS1M31Embedding.Total
end XRy_QueryTransport

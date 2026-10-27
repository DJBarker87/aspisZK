import XRn_PreparedBoundaries
open Aeneas Aeneas.Std Result
open XRn_Carriers XRn_ResultTransport XRn_ResultPair
set_option autoImplicit false
namespace XRn_PreparedScalars
open XRn_PreparedBoundaries

theorem scalar {H : Type} (D : C.D H) (t : C.T H) (row : U8)
 (payload : Slice U8) (nonzero : Bool) :
 mapR (fun p=>(p.1,ct p.2))
  (XRk_Release.transcript.Transcript.scalar (ed D) (et t) row payload nonzero)=
 AspisR1PublicPreparation.PreparedModel.scalar sampling D t row payload nonzero := by
 unfold XRk_Release.transcript.Transcript.scalar AspisR1PublicPreparation.PreparedModel.scalar
 rw [←XRn_TranscriptBlock.block]
 simp only [mapR_bind,bind_map]
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨block,after⟩ _
 simp only [sampling,mapR_bind,map_ok,
   XRk_Release.trace.value,AspisR1PublicPreparation.trace.value,bind_tc_ok]

theorem scalar_k {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p=>(cq p.1,ct p.2))
  (XRk_Release.transcript.Transcript.scalar_k (ed D) (et t) row payload)=
 AspisR1PublicPreparation.PreparedModel.scalar_k sampling D t row payload := by
 unfold XRk_Release.transcript.Transcript.scalar_k AspisR1PublicPreparation.PreparedModel.scalar_k
 rw [←XRn_TranscriptBlock.block]
 simp only [mapR_bind,bind_map]
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨block,after⟩ _
 rw [←XRn_QmSampler.sample]
 simp only [bind_map,mapR_bind]
 apply (bind_eq_iff _ _ _).mpr
 intro q _
 simp only [sampling,eq_cq,ct,
   XRk_Release.trace.value,AspisR1PublicPreparation.trace.value,bind_tc_ok,mapR_bind,map_ok]

#print axioms scalar
#print axioms scalar_k
end XRn_PreparedScalars

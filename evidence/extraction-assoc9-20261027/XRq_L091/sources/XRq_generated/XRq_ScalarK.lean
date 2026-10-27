import XRq_FromQm
import XRo_Join_PreparedScalars
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
namespace XRq_ScalarK
theorem source {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p=>(cq p.1,ct p.2))
  (XRn_Join_Release.transcript.Transcript.scalar_k (ed D) (et t) row payload)=
 AspisR1PublicPreparation.PreparedModel.scalar_k XRo_Join_Installed.actual.sampling D t row payload := by
 unfold XRn_Join_Release.transcript.Transcript.scalar_k AspisR1PublicPreparation.PreparedModel.scalar_k
 rw [←XRo_Join_TranscriptBlock.block]
 simp only [mapR_bind,bind_map]
 apply (bind_eq_iff _ _ _).mpr
 rintro ⟨block,after⟩ _
 change mapR (fun p=>(cq p.1,ct p.2))
   (do let q ← XRn_Join_Release.sampler.qm31_sample block
       let _ ← lift (UScalar.cast .Usize row)
       let _ ← aspis_core.field.wide_exact.WideExact.from_qm31 q
       ok (q,after)) =
   (do let q ← AspisR1PublicPreparation.sampler.qm31_sample block
       let _ ← lift (UScalar.cast .Usize row)
       let _ ← XRo_Join_Installed.actual.sampling.fromQm q
       ok (q,ct after))
 simp only [←XRo_Join_QmSampler.sample,bind_map,mapR_bind,map_ok,eq_cq,XRq_FromQm.source]


#print axioms source
end XRq_ScalarK

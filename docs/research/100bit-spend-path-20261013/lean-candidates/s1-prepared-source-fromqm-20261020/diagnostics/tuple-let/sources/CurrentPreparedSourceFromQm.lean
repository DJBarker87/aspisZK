import PreparedFromQmSourceBridge
import CurrentPreparedConcreteQueryRho
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.SourceFromQm
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedFromQmSourceBridge

theorem embedding_canonical (q : PrepQM) : Canonical (toClaimE (fromQmEmbedding q)) := by
  obtain ⟨h0,h1,h2,h3⟩ := AspisR1.C2HostEmbedding.canonical_bounded (prepToHostQM q)
  have hz : (0#u32).val<2147483647 := by decide
  unfold fromQmEmbedding hostToPrepWide AspisR1.C2HostEmbedding.embed
    AspisC2HostEmbedding.field.QM31.ZERO
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨hz,hz⟩,⟨hz,hz⟩⟩⟩

theorem scalar_k_source_success {H : Type} (sampling : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (before after : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (block : Array U8 32#usize)
    (hblock : transcript.Transcript.block D before row payload=ok (block,after)) :
    ∃ q : aspis_core.field.QM31,
      sampler.qm31_sample block=ok q ∧
      PreparedModel.scalar_k (withSourceFromQm sampling) D before row payload=ok (q,after) ∧
      Canonical (toClaimE (fromQmEmbedding q)) := by
  obtain ⟨q,hq,hcan,hcoords⟩ := SamplerTransport.sample_total block
  refine ⟨q,hq,?_,embedding_canonical q⟩
  simp only [PreparedModel.scalar_k,withSourceFromQm,hblock,hq,bind_tc_ok,
    fromQmSource_success,lift,trace.value]

#print axioms embedding_canonical
#print axioms scalar_k_source_success
end AspisR1ClaimPreparedBridge.SourceFromQm

import XRy_NarrowPrepare
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRy_PrepareCallbacks

theorem scalar (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b=AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (t : E.T H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
 mapR (fun p => (p.1,ct p.2))
   (XRq_OrdinaryScalar.scalar low (ed D) t row payload nonzero) =
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D (ct t) row payload nonzero := by
 simpa only [et_ct] using XRs_ClosedCallbacks.scalar low leaf D (ct t) row payload nonzero

theorem queries {H : Type} (D : C.D H) (t : E.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (inner id ce p.1,ct p.2))
   (XRn_Join_Release.transcript.Transcript.queries (ed D) t row payload) =
 XRo_Join_Installed.actual.sampling.queries D (ct t) row payload := by
 simpa only [et_ct] using XRy_Queries.queries D (ct t) row payload

theorem scalar_k {H : Type} (D : C.D H) (t : E.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (cq p.1,ct p.2))
   (XRn_Join_Release.transcript.Transcript.scalar_k (ed D) t row payload) =
 AspisR1PublicPreparation.PreparedModel.scalar_k XRo_Join_Installed.actual.sampling
   D (ct t) row payload := by
 simpa only [et_ct] using XRq_ScalarK.source D (ct t) row payload

theorem state {H : Type} (D : C.D H) (sem : C.Sem H) :
 XRn_Join_Release.r1_wire.SemanticTranscript.impl.state (ed D) (es sem).transcript =
 AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state D sem.transcript := rfl

#print axioms scalar
#print axioms queries
#print axioms scalar_k
#print axioms state
end XRy_PrepareCallbacks
end

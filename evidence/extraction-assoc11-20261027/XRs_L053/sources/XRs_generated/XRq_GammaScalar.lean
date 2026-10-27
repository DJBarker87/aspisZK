import XRq_OrdinaryScalar
import XRq_GammaAssociation
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XRq_GammaScalar

theorem source (add : XRq_GammaAssociation.AddAssociation)
 {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (p.1,ct p.2))
  (XRq_OrdinaryScalar.scalar AspisR1Post25Sampler.sampler.low_base_p_digits (ed D) (et t) row payload true) =
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
  D t row payload true := by
 unfold XRq_OrdinaryScalar.scalar AspisR1PublicPreparation.PreparedModel.scalar
 rw [←XRo_Join_TranscriptBlock.block]
 simp only [mapR_bind,bind_map,ite_true]
 apply congrArg (fun k => XRn_Join_Release.transcript.Transcript.block (ed D) (et t) row payload >>= k)
 funext p
 rcases p with ⟨block,after⟩
 change mapR (fun p => (p.1,ct p.2))
   (do let out ← XRq_SamplerInterface.gamma AspisR1Post25Sampler.sampler.low_base_p_digits block
       let i ← lift (UScalar.cast .Usize row)
       XRn_Join_Release.trace.value 4#u16 i out
       ok (out,after)) =
   (do let out ← XRo_Join_Installed.actual.sampling.gamma block
       let i ← lift (UScalar.cast .Usize row)
       AspisR1PublicPreparation.trace.value 4#u16 i out
       ok (out,ct after))
 rw [XRq_GammaAssociation.gamma add]
 simp only [mapR_bind,map_ok]
 rfl
#print axioms source
end XRq_GammaScalar

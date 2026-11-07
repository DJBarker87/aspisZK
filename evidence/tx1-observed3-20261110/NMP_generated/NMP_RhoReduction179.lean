import NMP_DigitCertificate179
import NGT_Reduction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_RhoReduction179
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open SamplerRepeatedPass SourceSamplerByteRank
/-- Build rhoReduction for every 32-byte block without a sampler-success
hypothesis. This is source/certificate support, not a whole native179 producer. -/
theorem source (block : Array U8 32#usize) :
 ∃ rho, NGT_Reduction.K block rho ∧ sampler.qm31_sample block=ok rho := by
 have trace := NMP_DigitCertificate179.source 4 (SamplerBytePass.digits block)
 obtain ⟨rho,call,canonical,value⟩ := SamplerTransport.sample_total block
 have coordinates : NGT_NBA_Rho.coordinates rho=SamplerNatModel.qm31Digits (rank block) := value
 have digits := NGT_NBA_Rho.four_digits block
  (run 4 (SamplerBytePass.digits block)).1 (run 4 (SamplerBytePass.digits block)).2 trace
 exact ⟨rho,⟨_,_,trace,coordinates.trans digits.symm⟩,call⟩
/-- The certificate is tied to the actual Block.value, never an independently
selected digest. Constructing the three-call Block still needs runtime laws. -/
theorem same_block {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (block : NGT_NBL_BlockTrace.Block D before row payload) :
 ∃ rho, NGT_Reduction.K block.value rho := by
 obtain ⟨rho,reduction,_⟩ := source block.value
 exact ⟨rho,reduction⟩
#print axioms source
#print axioms same_block
end AspisR1.NMP_RhoReduction179
end

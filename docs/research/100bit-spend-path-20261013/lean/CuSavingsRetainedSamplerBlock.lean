import CuSavingsRetainedSamplerBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSamplerBlock
open Aeneas Aeneas.Std Result CuSavingsRetainedSamplerBinding
/-- Choose the identical source Transcript.block leaf for scalar and scalar_k;
only nominal transcript/Digest carriers are copied. -/
@[reducible] def sameBlock (base : AspisR1CanonicalSampler.Shared)
    (common : AspisR1CuRho.ScalarKBlocks) : AspisR1CanonicalSampler.Shared :=
  {base with block := fun d t row payload => do
    let (bytes,after) ← common.block ⟨d.coremarkerCopyInst,d.digest⟩ (fromTranscript t) row payload
    .ok (bytes,transcript after)}
theorem block_source (base : AspisR1CanonicalSampler.Shared)
    (common : AspisR1CuRho.ScalarKBlocks) {H : Type}
    (d : AspisR1RhoPowerTail.aspis_core.Digest32 H)
    (t : AspisR1RhoPowerTail.transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (sameBlock base common).block (digest d) (transcript t) row payload =
      (do let (bytes,after) ← common.block d t row payload
          .ok (bytes,transcript after)) := rfl
#print axioms sameBlock
#print axioms block_source
end AspisR1.CuSavingsRetainedSamplerBlock

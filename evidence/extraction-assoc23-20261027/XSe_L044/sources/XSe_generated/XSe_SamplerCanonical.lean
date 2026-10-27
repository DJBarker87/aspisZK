import XSe_PowerCanonical
import XRo_Join_QmSampler
import SemanticCallSelectedCanonical
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_SamplerCanonical
/-- Canonicality of the non-retired QM31 sampler; this uses no low-base-P law. -/
theorem source (block : Array U8 32#usize) (q : aspis_core.field.QM31)
 (run : sampler.qm31_sample block=ok q) : XRp_PowersQAdd.CanonicalQ q := by
 have joined := XRo_Join_QmSampler.sample block
 rw [run] at joined
 have sampled : AspisR1PublicPreparation.sampler.qm31_sample block=ok (XRo_Join_Carriers.cq q) := joined.symm
 have old := AspisR1PublicPreparation.SamplerTransport.sample_toOld_success block _ sampled
 have canonical := AspisR1.ExtractedQM31SamplerCorrect.sample_canonical_of_success block _ old
 exact canonical
#print axioms source
end XSe_SamplerCanonical

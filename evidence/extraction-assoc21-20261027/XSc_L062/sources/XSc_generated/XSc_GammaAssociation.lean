import XRz_HybridSampler
import XRs_AddAssociation
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XSc_GammaAssociation
/-- The already checked all-input add association discharges the local gamma
adapter law; the excluded raw low sampler is never identified with this leaf. -/
theorem sampler (block : Array U8 32#usize) :
 XRq_SamplerInterface.gamma AspisR1Post25Sampler.sampler.low_base_p_digits block =
 XRo_Join_Installed.actual.sampling.gamma block :=
 XRq_GammaAssociation.gamma XRs_AddAssociation.add block
/-- Exact gamma scalar on the LPk-backed hybrid with no AddAssociation premise. -/
theorem scalar {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (p.1,ct p.2))
  (XRz_HybridSampler.scalar XRz_HybridSampler.adopted (ed D) (et t) row payload true)=
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling D t row payload true :=
 XRz_HybridSampler.gamma XRs_AddAssociation.add D t row payload
#print axioms sampler
#print axioms scalar
end XSc_GammaAssociation

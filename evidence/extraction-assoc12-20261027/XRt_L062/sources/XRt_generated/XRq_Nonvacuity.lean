import XRq_SamplerInterface
import XRp_SamplerNonvacuity
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRq_Nonvacuity
/-- The native-leaf premise has a model witness. This is consistency only,
not a certificate that the model is frozen native code. -/
theorem leaf_inhabited : ∃ native : XRq_SamplerInterface.Low,
 ∀ block, native block = AspisR1Post25Sampler.sampler.low_base_p_digits block :=
 ⟨AspisR1Post25Sampler.sampler.low_base_p_digits,fun _ => rfl⟩
#print axioms leaf_inhabited
#print axioms XRp_SamplerNonvacuity.both_succeed
end XRq_Nonvacuity

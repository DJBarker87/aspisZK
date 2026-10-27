import R1Z.PV_Canon_Carrier
import R1Z.ProverRwFullSampler
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
theorem sampler_total (bytes : Array U8 32#usize) :
    ∃ q, ProverRwFullSampler.selected bytes = .ok q ∧ Q q := by
  obtain ⟨q,hq,hc,_⟩ := ProverRwSamplerModel.sample_total bytes
  refine ⟨ProverRwFullSampler.fromSelected q,?_,hc⟩
  simp only [ProverRwFullSampler.selected,hq,bind_tc_ok]
#print axioms sampler_total
end R1Z.PV_Canon

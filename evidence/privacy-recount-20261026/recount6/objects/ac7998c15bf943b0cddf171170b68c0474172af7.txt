import R1Z.PV_Join_Canonical5
import R1Z.ProverRwFullSampler
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_SamplerCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5

theorem selected (bytes : Array U8 32#usize) :
    ∃ q, ProverRwFullSampler.selected bytes = .ok q ∧ Q q := by
  obtain ⟨q,hq,hc,_⟩ := ProverRwSamplerModel.sample_total bytes
  refine ⟨ProverRwFullSampler.fromSelected q,?_,hc⟩
  simp only [ProverRwFullSampler.selected,hq,bind_tc_ok]

#print axioms selected
end R1Z.PV_Join_SamplerCanonical5

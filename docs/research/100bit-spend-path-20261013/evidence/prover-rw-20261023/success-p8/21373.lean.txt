import R1Z.PV_OrdinaryDecodeBridge
import R1Z.ProverRwDictionarySamplers
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OrdinaryPolicyBridge
open Aeneas Aeneas.Std Result ProverRwDictionaryTower

theorem policy (block : Array U8 32#usize) :
    ProverRwDictionarySamplers.ordinary block =
      mapResult PV_OrdinaryNormalize.fromW (AspisR1Post25Sampler.sampler.ordinary_sample block) := by
  unfold ProverRwDictionarySamplers.ordinary ProverCommitPolicies25.ordinary
  cases h : AspisR1Post25Sampler.sampler.ordinary_sample block <;>
    simp only [h,bind_tc_ok,bind_tc_fail,bind_tc_div,mapResult] <;> rfl

theorem reference (block : Array U8 32#usize) :
    PV_OrdinarySource.sampler_owned.ordinary_sample block =
      ProverRwDictionarySamplers.ordinary block :=
  (PV_OrdinaryDecodeBridge.ordinary block).trans (policy block).symm
#print axioms policy
#print axioms reference
end R1Z.PV_OrdinaryPolicyBridge

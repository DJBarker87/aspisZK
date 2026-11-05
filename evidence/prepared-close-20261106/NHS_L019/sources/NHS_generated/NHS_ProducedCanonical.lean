import NHL_QueryDomain
import NHS_CanonicalPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_ProducedCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NHL_PreparedScalars NFN_LPi_FieldValues
/-- Consumer facts from the SAME emitted producer. This is an intermediate
model implication; NHS_PreparedPacket supplies its run instead of assuming a
native whole-constructor success. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
 (old scratch : NFW_PreparedControl.Scratch) (out : verifier.Prepared)
 (run : NGN_Emitted.prepared actual D sem v hash old=ok (.Ok out,scratch)) :
 canonE (NFW_SampledDomains.toNative out.gamma) ∧
 canonE (NFW_SampledDomains.toNative out.kappa) ∧
 (∀ x∈out.alpha.val,canonE (NFW_SampledDomains.toNative x)) ∧
 NBF_PowerStep.Canonical (NFW_PreparedPort.prepared out).rho ∧
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray
   (NFW_PreparedPort.map NFW_PreparedPort.e scratch)) := by
 have model := (NGN_EmittedEq.source actual D sem v hash old).symm.trans run
 have rho := NFW_ScalarRho.prepared actual D sem v hash out scratch old model
 rw [NHL_QueryDomain.dictionary] at model
 have both := AspisR1ClaimPreparedBridge.prepared_candidate_samplers_canonical
   actual.sampling D sem v hash out scratch old model
 obtain ⟨a,b,alpha,ca,cb⟩ := AspisR1ClaimPreparedBridge.prepared_candidate_alpha_pair
   actual.sampling D sem v hash out scratch old model
 refine ⟨NFW_SampledDomains.gamma_canonical out.gamma both.1,
   NFW_SampledDomains.gamma_canonical out.kappa both.2,?_,rho,
   (NFW_PrepareQuery.domains actual.sampling D sem v hash out scratch old model).1⟩
 intro x hx
 rw [alpha] at hx
 change x∈[a,b] at hx
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
 rcases hx with rfl|rfl
 · exact NFW_SampledDomains.gamma_canonical a ca
 · exact NFW_SampledDomains.gamma_canonical b cb
#print axioms source
end AspisR1.NHS_ProducedCanonical

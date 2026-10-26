import R1Z.PV_OrdinaryPolicyBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OrdinaryReferenceRank
open Aeneas Aeneas.Std Result
-- Owned-reference value/rank law. No full native sampler association is asserted.
theorem rank (block : Array U8 32#usize) :
    ∃ value, PV_OrdinarySource.sampler_owned.ordinary_sample block = ok value ∧
      ProverRwDictionarySamplers.decode value = R0C.ModuloField.fieldRank
        ⟨AspisR1.SourceSamplerByteRank.rank block % AspisCircleGroupOrder.P^8,
          Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ := by
  obtain ⟨v,hv,hd⟩ := ProverCommitPolicies25.ordinary_total (fun _ _ => .fail .panic) block
  refine ⟨ProverRwDictionarySamplers.fromPolicy v,?_,?_⟩
  · rw [PV_OrdinaryPolicyBridge.reference]
    unfold ProverRwDictionarySamplers.ordinary
    change ProverCommitPolicies25.ordinary block = ok v at hv
    rw [hv]
    rfl
  · simpa only [ProverRwDictionarySamplers.decode,ProverRwDictionarySamplers.roundtrip] using hd
#print axioms rank
end R1Z.PV_OrdinaryReferenceRank

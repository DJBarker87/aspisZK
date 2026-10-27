import PoolS2_MasterValidFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterValidExact
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_MasterValidFacts

theorem ready (m : Master) (h : Valid m) : run m = ok (.Ok ()) := by
  classical
  rcases h with ⟨pool,mint,token,domain,policy,bounds,repeated,first⟩
  have policyRun := PoolS2_PolicyExact.ready m.verifier_policy policy
  have bounded : m.last_checkpoint_lane_sequences.val.any (fun s => s > capacity) = false := by
    simpa using bounds
  cases hc : m.has_checkpoint
  · obtain ⟨seq,lanes⟩ := first hc
    simp [run,pool,mint,token,domain,policyRun,hc,seq,lanes]
  · have seq := repeated hc
    simp [run,pool,mint,token,domain,policyRun,hc,seq]
    simpa using bounds

theorem accepted_iff (m : Master) : run m = ok (.Ok ()) ↔ Valid m :=
  ⟨PoolS2_MasterValidFacts.accepted m,ready m⟩

#print axioms ready
#print axioms accepted_iff
end AspisR1.PoolS2_MasterValidExact
end

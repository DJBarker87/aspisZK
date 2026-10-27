import R1Z.PV_OptB_ChallengePair
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_ChallengeDifference
open R0P R0Z.HonestView
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- A common well-typed challenge has opposite VR1 verdicts on admitted
same-public witnesses. P_R1 acceptance and native reachability remain open. -/
theorem different (template : Challenges K) :
    ∃ a b : BuilderCanonical.Instance (K := K), ∃ ch : Challenges K,
      (BuilderSource.prover (K := K)).public a = (BuilderSource.prover (K := K)).public b ∧
      (MaskImageVR1.VR1 (K := K) (BuilderSource.prover (K := K)) ch a ↔
        ¬ MaskImageVR1.VR1 (K := K) (BuilderSource.prover (K := K)) ch b) := by
  obtain ⟨a,b,chi,same,opposite⟩ := PV_OptB_FixturePoleDifference.fixture (K := K)
  refine ⟨a,b,PV_OptB_ChallengePair.replace template 1 chi,same,?_⟩
  simpa only [MaskImageVR1.VR1,PV_OptB_ChallengePair.first,PV_OptB_ChallengePair.second] using opposite

#print axioms different
end R1Z.PV_OptB_ChallengeDifference

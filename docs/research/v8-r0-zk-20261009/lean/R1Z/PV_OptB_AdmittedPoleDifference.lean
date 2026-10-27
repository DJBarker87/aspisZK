import R1Z.PV_OptB_AdmittedTrace
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_AdmittedPoleDifference
open R0P AspisR1.SpendRelation R1Z.BuilderSpendRelation R1J.SpendWitnessMap
open PV_OptB_PathPoles
open PV_OptB_AdmittedFamily (admitted)
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]
attribute [local irreducible] PV_OptB_WitnessFamily.publicInput PV_OptB_WitnessFamily.witness

/-- Opposite pole verdicts on admitted same-public mathematical builders.
There is no assertion here about a native oracle or the P_R1 public gate. -/
theorem different (pub : Public M) (w : Wspend) (valid : RspendPlus pub w)
    (lam : K) (nonzero : lam ≠ 0) :
    ∃ a b : BuilderCanonical.Instance (K := K), ∃ chi : K,
      (BuilderSource.prover (K := K)).public a = (BuilderSource.prover (K := K)).public b ∧
      (R0Z.HonestValidity.NoPole ((BuilderSource.prover (K := K)).build a) lam chi ↔
        ¬ R0Z.HonestValidity.NoPole ((BuilderSource.prover (K := K)).build b) lam chi) := by
  obtain ⟨t,u,chi,same,opposite,_,_⟩ :=
    PV_OptB_DifferentNoPole.different_noPole pub w valid lam nonzero
  refine ⟨admitted pub w valid t,admitted pub w valid u,chi,?_,?_⟩
  · exact congrArg (mapPub (K := K)) same
  · rw [PV_OptB_AdmittedTrace.build_admitted,PV_OptB_AdmittedTrace.build_admitted]
    exact opposite

#print axioms different
end R1Z.PV_OptB_AdmittedPoleDifference

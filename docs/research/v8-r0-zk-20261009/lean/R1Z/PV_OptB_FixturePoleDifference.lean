import R1Z.PV_OptB_AdmittedPoleDifference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_FixturePoleDifference
open R0P
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Nonvacuous admitted-builder pole counterexample, still below the full
source failure claim. The fixture's root is allowed to change with its path;
the two selected resulting roots are equal to each other. -/
theorem fixture :
    ∃ a b : BuilderCanonical.Instance (K := K), ∃ chi : K,
      (BuilderSource.prover (K := K)).public a = (BuilderSource.prover (K := K)).public b ∧
      (R0Z.HonestValidity.NoPole ((BuilderSource.prover (K := K)).build a) 1 chi ↔
        ¬ R0Z.HonestValidity.NoPole ((BuilderSource.prover (K := K)).build b) 1 chi) :=
  PV_OptB_AdmittedPoleDifference.different
    (PV_Src_Fixture_FixtureRecords.fixturePublic true)
    (PV_Src_Fixture_FixtureRecords.witness true)
    PV_Src_Fixture_FixtureRecords.withdrawal_spendPlus 1 one_ne_zero

#print axioms fixture
end R1Z.PV_OptB_FixturePoleDifference
